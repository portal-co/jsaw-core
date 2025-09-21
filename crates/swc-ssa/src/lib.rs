use std::{
    collections::{BTreeMap, BTreeSet},
    convert::Infallible,
    iter::{empty, once},
    mem::take,
};

use anyhow::Context;
use cfg_traits::Term;
use id_arena::{Arena, Id};
use portal_jsc_common::Asm;
use portal_jsc_swc_util::SemanticCfg;
use ssa_traits::HasChainableValues;
use swc_common::Span;
use swc_ecma_ast::{Id as Ident, Lit, TsType, TsTypeAnn, TsTypeParamDecl, UnaryOp};
use swc_tac::{Item, TBlock, TCallee, TCfg, TFunc, TStmt, TTerm, ValFlags};
use swc_tac::{LId, inlinable};
pub mod consts;
// pub mod idw;
pub mod conv;
pub mod impls;
pub mod opt_stub;
pub mod rew;
pub mod simplify;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum EdgeKind {
    Forward,
    Backward,
}
impl SCfg {
    pub fn block_edges(&mut self, mode: EdgeKind) {
        for block_index in self.blocks.iter().map(|a| a.0).collect::<Vec<_>>() {
            let mut postcedent = take(&mut self.blocks[block_index].postcedent);
            for target in postcedent.targets_mut() {
                if match mode {
                    EdgeKind::Backward => target.block.index() <= block_index.index(),
                    EdgeKind::Forward => target.block.index() >= block_index.index(),
                } {
                    for arg in target.args.iter_mut() {
                        let value = self.values.alloc(SValueW {
                            value: SValue::EdgeBlocker {
                                value: *arg,
                                span: None,
                            },
                        });
                        self.blocks[block_index].stmts.push(value);
                        *arg = value;
                    }
                }
            }
            self.blocks[block_index].postcedent = postcedent;
        }
    }
    pub fn unblock_edges(&mut self) {
        for (_, val) in self.values.iter_mut() {
            if let SValue::EdgeBlocker { value: x, span } = &val.value {
                val.value = SValue::Item {
                    item: Item::Just { id: *x },
                    span: *span,
                }
            }
        }
    }
    pub fn equate_items(&mut self) {
        let mut map = BTreeMap::new();
        for (a, b) in self.values.iter() {
            if let SValue::Item {
                item: Item::Just { id },
                span,
            } = &b.value
            {
                map.insert(a, *id);
            }
        }
        for (_, b) in self.values.iter_mut() {
            for r in b.value.vals_mut() {
                while let Some(v2) = map.get(r) {
                    *r = *v2
                }
            }
        }
        for (_, b) in self.blocks.iter_mut() {
            for t in b.postcedent.targets_mut() {
                for r in t.args.iter_mut() {
                    while let Some(v2) = map.get(r) {
                        *r = *v2
                    }
                }
            }
        }
        for (_, b) in self.blocks.iter_mut() {
            b.stmts.retain(|a| !map.contains_key(a));
        }
    }
    pub fn strip_useless(&mut self) {
        let mut set = BTreeSet::new();
        for (val, SValueW { value }) in self.values.iter_mut() {
            match value {
                SValue::Item { item, span } => match item {
                    Item::Func { func: _, arrow: _ } | Item::Undef | Item::Lit { lit: _ } => {
                        set.insert(val);
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        for (_, b) in self.values.iter_mut() {
            for r in b.value.vals_mut() {
                set.remove(r);
            }
        }
        for (_, b) in self.blocks.iter_mut() {
            for t in b.postcedent.targets_mut() {
                for r in t.args.iter_mut() {
                    set.remove(r);
                }
            }
        }
        for (_, b) in self.blocks.iter_mut() {
            b.stmts.retain(|a| !set.contains(a));
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SFunc {
    pub cfg: SCfg,
    pub entry: Id<SBlock>,
    pub is_generator: bool,
    pub is_async: bool,
    pub ts_params: Vec<Option<TsType>>,
}

impl TryFrom<TFunc> for SFunc {
    type Error = anyhow::Error;

    fn try_from(value: TFunc) -> Result<Self, Self::Error> {
        TryFrom::try_from(&value)
    }
}
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct SCfg {
    pub blocks: Arena<SBlock>,
    pub values: Arena<SValueW>,
    pub ts: BTreeMap<Id<SValueW>, TsType>,
    pub decls: BTreeSet<Ident>,
    pub generics: Option<TsTypeParamDecl>,
    pub ts_retty: Option<TsTypeAnn>,
}
impl SCfg {
    pub fn inputs(&self, block: Id<SBlock>, param: usize) -> impl Iterator<Item = Id<SValueW>> {
        return self.blocks.iter().flat_map(move |k| {
            k.1.postcedent
                .term
                .targets()
                .filter_map(move |t| {
                    if t.block == block {
                        t.args.get(param).cloned()
                    } else {
                        None
                    }
                })
                .chain(k.1.postcedent.catch.targets().filter_map(move |t| {
                    if t.block == block {
                        t.args.get(param.wrapping_sub(1)).cloned()
                    } else {
                        None
                    }
                }))
        });
    }
    pub fn input(&self, block: Id<SBlock>, param: usize) -> Option<Id<SValueW>> {
        let mut i = self.inputs(block, param);
        let a = i.next()?;
        for j in i {
            if j != a {
                return None;
            }
        }
        return Some(a);
    }
    pub fn taints_object(&self, a: &Id<SValueW>) -> bool {
        return self.blocks.iter().any(|s| {
            s.1.stmts.iter().any(|s| {
                let mut s = *s;
                loop {
                    return match &self.values[s].value {
                        SValue::Assign { target, val } => target.taints_object(a),
                        SValue::Item { item, span } => item.taints_object(a),
                        SValue::Param { block, idx, ty } => match self.input(*block, *idx) {
                            None => true,
                            Some(a) => {
                                s = a;
                                continue;
                            }
                        },
                        _ => true,
                    };
                }
            }) || s.1.postcedent.term.taints_object(a)
        });
    }
    pub fn refs(&self) -> BTreeSet<Ident> {
        return self
            .values
            .iter()
            .flat_map(|(a, b)| match &b.value {
                SValue::LoadId(target) | SValue::StoreId { target, val: _ } => {
                    [target.clone()].into_iter().collect::<BTreeSet<Ident>>()
                }
                SValue::Item { item, span } => {
                    item.funcs().flat_map(|func| func.cfg.externals()).collect()
                }
                _ => Default::default(),
            })
            .collect();
    }
    pub fn externals(&self) -> BTreeSet<Ident> {
        return self
            .refs()
            .into_iter()
            .filter(|a| !self.decls.contains(&*a))
            .collect();
    }
}
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct SBlock {
    pub params: Vec<(Id<SValueW>, ())>,
    pub stmts: Vec<Id<SValueW>>,
    pub postcedent: SPostcedent,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SPostcedent<I = Id<SValueW>, B = Id<SBlock>> {
    pub term: STerm<I, B>,
    pub catch: SCatch<I, B>,
}
impl<I, B> Default for SPostcedent<I, B> {
    fn default() -> Self {
        Self {
            term: Default::default(),
            catch: Default::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SValue<I = Id<SValueW>, B = Id<SBlock>, F = SFunc> {
    Param {
        block: B,
        idx: usize,
        ty: (),
    },
    Item {
        item: Item<I, F>,
        span: Option<Span>,
    },
    Assign {
        target: LId<I>,
        val: I,
    },
    LoadId(Ident),
    StoreId {
        target: Ident,
        val: I,
    },
    EdgeBlocker {
        value: I,
        span: Option<Span>,
    },
}
impl<I, B, F> SValue<I, B, F> {
    pub fn nothrow(&self) -> bool {
        match self {
            SValue::Param { block, idx, ty } => true,
            SValue::Item { item, span } => item.nothrow(),
            SValue::Assign { target, val } => target.nothrow(),
            SValue::LoadId(_) => true,
            SValue::StoreId { target, val } => true,
            SValue::EdgeBlocker { value, span } => true,
        }
    }
}
impl<I: Copy, B, F> SValue<I, B, F> {
    pub fn vals<'a>(&'a self) -> Box<dyn Iterator<Item = I> + 'a> {
        match self {
            SValue::Param { block, idx, ty } => Box::new(empty()),
            SValue::Item { item, span } => Box::new(item.refs().map(|a| *a)),
            SValue::Assign { target, val } => {
                let v = once(*val);
                let w: Box<dyn Iterator<Item = &I> + '_> = match target {
                    LId::Id { id } => todo!(),
                    LId::Member { obj, mem } => Box::new([obj, &mem[0]].into_iter()),
                    _ => todo!(),
                };
                Box::new(v.chain(w.cloned()))
            }
            SValue::LoadId(_) => Box::new(empty()),
            SValue::StoreId { target, val } => Box::new(once(*val)),
            SValue::EdgeBlocker { value: a, span } => Box::new(once(*a)),
        }
    }
}
impl<I, B, F> SValue<I, B, F> {
    pub fn as_ref(&self) -> SValue<&I, &B, &F> {
        match self {
            SValue::Param { block, idx, ty } => SValue::Param {
                block,
                idx: *idx,
                ty: *ty,
            },
            SValue::Item { item, span } => SValue::Item {
                item: item.as_ref(),
                span: *span,
            },
            SValue::Assign { target, val } => SValue::Assign {
                target: target
                    .as_ref()
                    .map2(&mut (), &mut |_, a| Ok::<_, Infallible>(a), &mut |_, b| {
                        Ok([&b[0]])
                    })
                    .unwrap(),
                val,
            },
            SValue::LoadId(v) => SValue::LoadId(v.clone()),
            SValue::StoreId { target, val } => SValue::StoreId {
                target: target.clone(),
                val,
            },
            SValue::EdgeBlocker { value: v, span } => SValue::EdgeBlocker {
                value: v,
                span: *span,
            },
        }
    }
    pub fn as_mut(&mut self) -> SValue<&mut I, &mut B, &mut F> {
        match self {
            SValue::Param { block, idx, ty } => SValue::Param {
                block,
                idx: *idx,
                ty: *ty,
            },
            SValue::Item { item, span } => SValue::Item {
                item: item.as_mut(),
                span: *span,
            },
            SValue::Assign { target, val } => SValue::Assign {
                target: target
                    .as_mut()
                    .map2(&mut (), &mut |_, a| Ok::<_, Infallible>(a), &mut |_, b| {
                        Ok([&mut b[0]])
                    })
                    .unwrap(),
                val,
            },
            SValue::LoadId(v) => SValue::LoadId(v.clone()),
            SValue::StoreId { target, val } => SValue::StoreId {
                target: target.clone(),
                val,
            },
            SValue::EdgeBlocker { value: v, span } => SValue::EdgeBlocker {
                value: v,
                span: *span,
            },
        }
    }
    pub fn map<J, C, G, X, E>(
        self,
        cx: &mut X,
        ident: &mut (dyn FnMut(&mut X, I) -> Result<J, E> + '_),
        block_: &mut (dyn FnMut(&mut X, B) -> Result<C, E> + '_),
        fun: &mut (dyn FnMut(&mut X, F) -> Result<G, E> + '_),
    ) -> Result<SValue<J, C, G>, E> {
        Ok(match self {
            SValue::Param { block, idx, ty } => SValue::Param {
                block: block_(cx, block)?,
                idx,
                ty,
            },
            SValue::Item { item, span } => SValue::Item {
                item: item.map2(cx, ident, fun)?,
                span,
            },
            SValue::Assign { target, val } => SValue::Assign {
                target: target.map(&mut |a| ident(cx, a))?,
                val: ident(cx, val)?,
            },
            SValue::LoadId(a) => SValue::LoadId(a),
            SValue::StoreId { target, val } => SValue::StoreId {
                target,
                val: ident(cx, val)?,
            },
            SValue::EdgeBlocker { value: i, span } => SValue::EdgeBlocker {
                value: ident(cx, i)?,
                span,
            },
        })
    }
    pub fn vals_ref<'a>(&'a self) -> Box<dyn Iterator<Item = &'a I> + 'a> {
        match self {
            SValue::Param { block, idx, ty } => Box::new(empty()),
            SValue::Item { item, span } => Box::new(item.refs()),
            SValue::Assign { target, val } => {
                let v = once(val);
                let w: Box<dyn Iterator<Item = &I> + '_> = match target {
                    LId::Id { id } => todo!(),
                    LId::Member { obj, mem } => Box::new([obj, &mem[0]].into_iter()),
                    _ => todo!(),
                };
                Box::new(v.chain(w))
            }
            SValue::LoadId(_) => Box::new(empty()),
            SValue::StoreId { target, val } => Box::new(once(val)),
            SValue::EdgeBlocker { value: a, span } => Box::new(once(a)),
        }
    }
    pub fn vals_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut I> + 'a> {
        match self {
            SValue::Param { block, idx, ty } => Box::new(empty()),
            SValue::Item { item, span } => item.refs_mut(),
            SValue::Assign { target, val } => {
                let v = once(val);
                let w: Box<dyn Iterator<Item = &mut I> + '_> = match target {
                    LId::Id { id } => todo!(),
                    LId::Member { obj, mem } => Box::new([obj, &mut mem[0]].into_iter()),
                    _ => todo!(),
                };
                Box::new(v.chain(w))
            }
            SValue::LoadId(_) => Box::new(empty()),
            SValue::StoreId { target, val } => Box::new(once(val)),
            SValue::EdgeBlocker { value: a, span } => Box::new(once(a)),
        }
    }
}
#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SValueW {
    pub value: SValue,
}
impl From<SValue> for SValueW {
    fn from(value: SValue) -> Self {
        Self { value }
    }
}
impl From<SValueW> for SValue {
    fn from(value: SValueW) -> Self {
        value.value
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SCatch<I = Id<SValueW>, B = Id<SBlock>> {
    Throw,
    Just { target: STarget<I, B> },
}
impl<I, B> Default for SCatch<I, B> {
    fn default() -> Self {
        Self::Throw
    }
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct STarget<I = Id<SValueW>, B = Id<SBlock>> {
    pub block: B,
    pub args: Vec<I>,
}
pub type STerm<I = Id<SValueW>, B = Id<SBlock>> = TTerm<STarget<I, B>, I>;
// #[derive(Clone, Debug, PartialEq, Eq)]
// #[non_exhaustive]
// pub enum STerm<I = Id<SValueW>, B = Id<SBlock>> {
//     Throw(I),
//     Return(Option<I>),
//     Jmp(STarget<I, B>),
//     CondJmp {
//         cond: I,
//         if_true: STarget<I, B>,
//         if_false: STarget<I, B>,
//     },
//     Switch {
//         x: I,
//         blocks: Vec<(I, STarget<I, B>)>,
//         default: STarget<I, B>,
//     },
//     Default,
// }
// impl<I, B> Default for STerm<I, B> {
//     fn default() -> Self {
//         Self::Default
//     }
// }
impl SCfg {
    pub fn add_blockparam(&mut self, k: Id<SBlock>) -> Id<SValueW> {
        let val = SValue::Param {
            block: k,
            idx: self.blocks[k].params.len(),
            ty: (),
        };
        let val = self.values.alloc(val.into());
        self.blocks[k].params.push((val, ()));
        return val;
    }
    pub fn do_consts(&mut self, semantic: &SemanticCfg) {
        self.unblock_edges();
        let mut m = BTreeMap::new();
        let mut aliases = BTreeMap::new();
        for (k, v) in self.values.iter() {
            if let SValue::Param { block, idx, ty } = &v.value {
                if let Some(i) = self.input(*block, *idx) {
                    aliases.insert(k, i);
                }
                continue;
            };
            if let Some(v) = v.value.const_in(semantic, self, true) {
                m.insert(k, v);
                continue;
            };
            if let SValue::Item {
                item: Item::Just { id },
                span,
            } = &v.value
            {
                aliases.insert(k, *id);
            }
        }
        for (k, v) in m {
            self.values[k].value = SValue::Item {
                item: Item::Lit { lit: v },
                span: None,
            };
        }
        for r in self.blocks.iter_mut().flat_map(|a| {
            a.1.stmts
                .iter_mut()
                .chain(a.1.postcedent.values_chain_mut())
        }) {
            while let Some(x) = aliases.get(r) {
                *r = *x
            }
        }
    }
}
