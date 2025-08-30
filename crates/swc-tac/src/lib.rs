use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::convert::Infallible;
use std::iter::{empty, once};
use std::mem::take;

use anyhow::Context;
use arena_traits::IndexAlloc;
use bitflags::bitflags;
use either::Either;
use id_arena::{Arena, Id};
use lam::LAM;
use linearize::{StaticMap, static_map};
use portal_jsc_common::{Asm, Native};
use portal_jsc_swc_util::brighten::Purity;
use portal_jsc_swc_util::{ImportMapper, ResolveNatives, SemanticCfg, SemanticFlags, ses_method};
use portal_solutions_swibb::ConstCollector;
use ssa_impls::dom::{dominates, domtree};
use swc_atoms::Atom;
use swc_cfg::{Block, Catch, Cfg, Func};
use swc_common::{EqIgnoreSpan, Mark, Span, Spanned, SyntaxContext};
use swc_ecma_ast::{
    AssignExpr, AssignOp, AssignTarget, BinaryOp, Bool, Callee, Class, ClassMember,
    ComputedPropName, CondExpr, Expr, Function, Lit, MemberExpr, MemberProp, Number, Param, Pat,
    SimpleAssignTarget, Stmt, Str, TsType, TsTypeAnn, TsTypeParamDecl, UnaryOp,
};

use swc_ecma_ast::Id as Ident;

use crate::consts::{ItemGetter, ItemGetterExt};

pub mod consts;
pub mod conv;
pub mod lam;
pub mod prepa;
pub mod rew;
pub mod splat;
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Private {
    pub sym: Atom,
    pub ctxt: SyntaxContext,
    pub span: Span,
}
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum LId<I = Ident, M = [I; 1]> {
    Id { id: I },
    Member { obj: I, mem: M },
    Private { obj: I, id: Private },
}
impl<I> LId<I> {
    pub fn map<J, E>(self, f: &mut impl FnMut(I) -> Result<J, E>) -> Result<LId<J>, E> {
        self.map2(f, &mut |cx, a| cx(a), &mut |cx, [a]| cx(a).map(|b| [b]))
    }
}
impl<I, M> LId<I, M> {
    pub fn as_ref<'a>(&'a self) -> LId<&'a I, &'a M>
where
        // &'a M: IntoIterator<Item = &'a I>,
    {
        match self {
            LId::Id { id } => LId::Id { id },
            LId::Member { obj, mem } => LId::Member { obj, mem },
            LId::Private { obj, id } => LId::Private {
                obj,
                id: id.clone(),
            },
        }
    }
    pub fn as_mut<'a>(&'a mut self) -> LId<&'a mut I, &'a mut M>
where
        // &'a mut M: IntoIterator<Item = &'a mut I>,
    {
        match self {
            LId::Id { id } => LId::Id { id },
            LId::Member { obj, mem } => LId::Member { obj, mem },
            LId::Private { obj, id } => LId::Private {
                obj,
                id: id.clone(),
            },
        }
    }
    pub fn refs(self) -> impl Iterator<Item = I>
    where
        M: IntoIterator<Item = I>,
    {
        match self {
            LId::Id { id } => Either::Left(once(id)),
            LId::Member { obj, mem } => Either::Right(once(obj).chain(mem)),
            LId::Private { id, obj } => Either::Left(once(obj)),
        }
    }
    pub fn map2<Cx, J, N, E>(
        self,
        cx: &mut Cx,
        f: &mut (dyn FnMut(&mut Cx, I) -> Result<J, E> + '_),
        g: &mut (dyn FnMut(&mut Cx, M) -> Result<N, E> + '_),
    ) -> Result<LId<J, N>, E> {
        Ok(match self {
            LId::Id { id } => LId::Id { id: f(cx, id)? },
            LId::Member { obj, mem } => LId::Member {
                obj: f(cx, obj)?,
                mem: g(cx, mem)?,
            },
            LId::Private { id, obj } => LId::Private {
                id,
                obj: f(cx, obj)?,
            },
        })
    }
}

#[cfg(feature = "simpl")]
pub mod simpl;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, linearize::Linearize)]
#[non_exhaustive]
pub enum ImportMapperReq {
    // Native,
}

pub fn imp(a: MemberProp) -> Expr {
    match a {
        swc_ecma_ast::MemberProp::Ident(ident_name) => {
            let e = Expr::Lit(Lit::Str(Str {
                span: ident_name.span,
                value: ident_name.sym,
                raw: None,
            }));
            e
        }
        swc_ecma_ast::MemberProp::PrivateName(private_name) => {
            todo!()
        }
        swc_ecma_ast::MemberProp::Computed(computed_prop_name) => *computed_prop_name.expr,
    }
}
bitflags! {
    #[repr(transparent)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
    pub struct ValFlags: u64{
        const SSA_LIKE = 0x1;
    }
}
bitflags! {
    #[repr(transparent)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
    pub struct MemberFlags: u64{
        const STATIC = 0x1;
        const PRIVATE = 0x2;
    }
}
#[derive(Clone, Debug)]
pub struct TFunc {
    pub cfg: TCfg,
    pub entry: Id<TBlock>,
    pub params: Vec<Ident>,
    pub ts_params: Vec<Option<TsType>>,
    pub is_generator: bool,
    pub is_async: bool,
}
#[derive(Clone)]
#[non_exhaustive]
pub struct Mapper<'a> {
    pub import_mapper: StaticMap<ImportMapperReq, Option<&'a (dyn ImportMapper + 'a)>>,
    pub semantic: &'a SemanticCfg,
    pub privates: &'a BTreeMap<Atom, SyntaxContext>,
    pub consts: Option<&'a ConstCollector>,
}
pub fn mapped<T>(a: impl FnOnce(Mapper<'_>) -> T) -> T {
    return a(Mapper {
        import_mapper: static_map! {_ => None},
        semantic: &SemanticCfg::default(),
        privates: &BTreeMap::new(),
        consts: None,
    });
}
impl<'a> Mapper<'a> {
    pub fn bud(&self) -> Mapper<'_> {
        Mapper {
            import_mapper: static_map! {a =>self.import_mapper[a].as_deref()},
            semantic: self.semantic,
            privates: self.privates,
            consts: self.consts.as_deref(),
        }
    }
}

impl<'a> TryFrom<&'a Func> for TFunc {
    type Error = anyhow::Error;

    fn try_from(value: &'a Func) -> Result<Self, Self::Error> {
        mapped(|m| TFunc::try_from_with_mapper(value, m))
    }
}
impl TryFrom<Func> for TFunc {
    type Error = anyhow::Error;

    fn try_from(value: Func) -> Result<Self, Self::Error> {
        TryFrom::try_from(&value)
    }
}
impl TryFrom<Function> for TFunc {
    type Error = anyhow::Error;

    fn try_from(value: Function) -> Result<Self, Self::Error> {
        let a: Func = value.try_into()?;
        return a.try_into();
    }
}
#[derive(Default, Clone, Debug)]
pub struct TCfg {
    pub blocks: Arena<TBlock>,
    pub regs: LAM<()>,
    pub decls: BTreeSet<Ident>,
    pub type_annotations: BTreeMap<Ident, TsType>,
    pub generics: Option<TsTypeParamDecl>,
    pub ts_retty: Option<TsTypeAnn>,
}
pub trait Externs<I> {
    fn externs(&self) -> impl Iterator<Item = I>;
}
impl TFunc {
    pub fn remark(&mut self) {
        let d: BTreeMap<Option<Id<TBlock>>, Id<TBlock>> = domtree(&*self);
        self.cfg.remark_with_domtree(d);
    }
}
impl TCfg {
    pub fn remark_with_domtree(&mut self, d: BTreeMap<Option<Id<TBlock>>, Id<TBlock>>) {
        let mut a: BTreeMap<LId, usize> = BTreeMap::new();
        for (b, s) in self.blocks.iter() {
            'a: for s in &s.stmts {
                if match &s.left {
                    LId::Id { id } => !self.decls.contains(&id),
                    LId::Member { obj, mem } => {
                        !self.decls.contains(&obj) || !self.decls.contains(&mem[0])
                    }
                    _ => todo!(),
                } {
                    continue;
                }
                if *a.entry(s.left.clone()).or_default() > 1 {
                    continue 'a;
                }
                if let LId::Id { id } = &s.left {
                    for (b2, t) in self.blocks.iter() {
                        for t in t.stmts.iter() {
                            if t.right.refs().any(|r| *r == *id) {
                                if !dominates::<TFunc>(&d, Some(b), Some(b2)) {
                                    *a.entry(s.left.clone()).or_default() += 2usize;
                                    continue 'a;
                                }
                            }
                        }
                    }

                    *a.entry(s.left.clone()).or_default() += 1usize;
                }
            }
        }
        // let d =

        for s in self.blocks.iter_mut().flat_map(|a| &mut a.1.stmts) {
            if match &s.left {
                LId::Id { id } => !self.decls.contains(&id),
                LId::Member { obj, mem } => {
                    !self.decls.contains(&obj) || !self.decls.contains(&mem[0])
                }
                _ => todo!(),
            } {
                continue;
            }
            if a.remove(&s.left) == Some(1) {
                s.flags |= ValFlags::SSA_LIKE
            } else {
                s.flags &= !ValFlags::SSA_LIKE;
            }
        }
    }
    pub fn strip_useless(&mut self) {
        let mut set = BTreeSet::new();
        for (_, k) in self.blocks.iter() {
            for l in k.stmts.iter() {
                match &l.right {
                    Item::Func { func: _, arrow: _ } | Item::Undef | Item::Lit { lit: _ } => {
                        match &l.left {
                            LId::Id { id } => {
                                set.insert(id.clone());
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            }
        }
        for (_, k) in self.blocks.iter() {
            for l in k.stmts.iter() {
                for r in l
                    .right
                    .refs()
                    .cloned()
                    .chain(l.right.funcs().flat_map(|f| f.cfg.externs()))
                {
                    set.remove(&r);
                }
                match &l.left {
                    LId::Id { id } => {}
                    LId::Member { obj, mem } => {
                        set.remove(obj);
                        set.remove(&mem[0]);
                    }
                    LId::Private { obj, id } => {
                        set.remove(obj);
                    }
                    _ => {}
                }
            }
        }
        for (_, k) in self.blocks.iter_mut() {
            for l in take(&mut k.stmts) {
                match &l.left {
                    LId::Id { id } => {
                        if set.contains(id) {
                            continue;
                        }
                    }
                    _ => {}
                }
                k.stmts.push(l);
            }
        }
    }
    pub fn def(&self, i: LId<Ident>) -> Option<&Item> {
        self.blocks.iter().flat_map(|a| &a.1.stmts).find_map(|a| {
            if a.left == i && a.flags.contains(ValFlags::SSA_LIKE) {
                Some(&a.right)
            } else {
                None
            }
        })
    }
    pub fn def_mut(&mut self, i: LId<Ident>) -> Option<&mut Item> {
        self.blocks
            .iter_mut()
            .flat_map(|a| &mut a.1.stmts)
            .find_map(|a| {
                if a.left == i && a.flags.contains(ValFlags::SSA_LIKE) {
                    Some(&mut a.right)
                } else {
                    None
                }
            })
    }
    pub fn refs<'a>(&'a self) -> impl Iterator<Item = Ident> + 'a {
        let a = self.blocks.iter().flat_map(|k| {
            let i: Box<dyn Iterator<Item = Ident> + '_> = match &k.1.post.term {
                TTerm::Return(a) => Box::new(a.iter().cloned()),
                TTerm::Throw(b) => Box::new(Some(b.clone()).into_iter()),
                TTerm::Jmp(id) => Box::new(std::iter::empty()),
                TTerm::CondJmp {
                    cond,
                    if_true,
                    if_false,
                } => Box::new(once(cond.clone())),
                TTerm::Switch { x, blocks, default } => {
                    Box::new(once(x.clone()).chain(blocks.iter().map(|a| a.0.clone())))
                }
                TTerm::Default => Box::new(std::iter::empty()),
            };
            i.chain(k.1.stmts.iter().flat_map(
                |TStmt {
                     left: a,
                     flags: _,
                     right: b,
                     span: _,
                 }| {
                    let a = a.as_ref().refs().cloned();
                    let b = b
                        .refs()
                        .cloned()
                        .chain(b.funcs().flat_map(|a| a.cfg.externs()));
                    a.chain(b)
                },
            ))
        });
        return a;
    }
    pub fn simplify_justs(&mut self) {
        let mut redo = true;
        while take(&mut redo) {
            for ref_ in self.refs().collect::<BTreeSet<_>>() {
                redo = redo | self.simplify_just(ref_);
            }
        }
    }
    pub fn externs<'a>(&'a self) -> Box<dyn Iterator<Item = Ident> + 'a> {
        Box::new(self.refs().filter(|a| !self.decls.contains(a)))
    }
    pub fn update(&mut self) {
        for x in self.blocks.iter() {
            for k in x.1.stmts.iter() {
                k.left
                    .clone()
                    .map(&mut |a| {
                        self.regs[a] = ();
                        Ok::<(), Infallible>(())
                    })
                    .unwrap();
            }
        }
    }
    pub fn has_this(&self) -> bool {
        self.blocks.iter().any(|k| {
            k.1.stmts.iter().any(|s| {
                matches!(&s.right, Item::This)
                    || match &s.right {
                        Item::Func { func, arrow: true } => func.cfg.has_this(),
                        _ => false,
                    }
            })
        })
    }
}
impl Externs<Ident> for TCfg {
    fn externs(&self) -> impl Iterator<Item = Ident> {
        TCfg::externs(self)
    }
}
#[derive(Clone, Debug)]
pub struct TStmt {
    pub left: LId,
    pub flags: ValFlags,
    pub right: Item,
    pub span: Span,
}
#[derive(Clone, Default, Debug)]
pub struct TBlock {
    pub stmts: Vec<TStmt>,
    pub post: TPostecedent,
}
#[derive(Clone, Default, Debug)]
pub struct TPostecedent {
    pub catch: TCatch,
    pub term: TTerm,
    pub orig_span: Option<Span>,
}
pub mod impls;
#[derive(Clone, Default, Debug)]
pub enum TCatch {
    #[default]
    Throw,
    Jump {
        pat: Ident,
        k: Id<TBlock>,
    },
}
#[derive(Clone, Default, Debug)]
pub enum TTerm {
    Return(Option<Ident>),
    Throw(Ident),
    Jmp(Id<TBlock>),
    CondJmp {
        cond: Ident,
        if_true: Id<TBlock>,
        if_false: Id<TBlock>,
    },
    Switch {
        x: Ident,
        blocks: HashMap<Ident, Id<TBlock>>,
        default: Id<TBlock>,
    },
    #[default]
    Default,
}
#[derive(Clone, Ord, PartialEq, PartialOrd, Eq, Debug)]
#[non_exhaustive]
pub enum PropKey<I = Ident> {
    Lit(Ident),
    Computed(I),
}

impl<I> PropKey<I> {
    pub fn as_ref(&self) -> PropKey<&I> {
        match self {
            PropKey::Lit(a) => PropKey::Lit(a.clone()),
            PropKey::Computed(c) => PropKey::Computed(c),
        }
    }
    pub fn as_mut(&mut self) -> PropKey<&mut I> {
        match self {
            PropKey::Lit(a) => PropKey::Lit(a.clone()),
            PropKey::Computed(c) => PropKey::Computed(c),
        }
    }
    pub fn map<J: Ord, E>(
        self,
        f: &mut (dyn FnMut(I) -> Result<J, E> + '_),
    ) -> Result<PropKey<J>, E> {
        Ok(match self {
            PropKey::Lit(l) => PropKey::Lit(l),
            PropKey::Computed(x) => PropKey::Computed(f(x)?),
        })
    }
}
#[derive(Clone, Ord, PartialEq, PartialOrd, Eq, Debug)]
#[non_exhaustive]
pub enum PropVal<I, F> {
    Item(I),
    Getter(F),
    Setter(F),
    Method(F),
}
impl<I, F> PropVal<I, F> {
    pub fn as_ref(&self) -> PropVal<&I, &F> {
        match self {
            PropVal::Item(a) => PropVal::Item(a),
            PropVal::Getter(f) => PropVal::Getter(f),
            PropVal::Setter(f) => PropVal::Setter(f),
            PropVal::Method(f) => PropVal::Method(f),
        }
    }
    pub fn as_mut(&mut self) -> PropVal<&mut I, &mut F> {
        match self {
            PropVal::Item(a) => PropVal::Item(a),
            PropVal::Getter(f) => PropVal::Getter(f),
            PropVal::Setter(f) => PropVal::Setter(f),
            PropVal::Method(f) => PropVal::Method(f),
        }
    }
    pub fn map<I2, F2, Cx: ?Sized, E>(
        self,
        cx: &mut Cx,
        i: &mut (dyn FnMut(&mut Cx, I) -> Result<I2, E> + '_),
        f: &mut (dyn FnMut(&mut Cx, F) -> Result<F2, E> + '_),
    ) -> Result<PropVal<I2, F2>, E> {
        Ok(match self {
            PropVal::Item(a) => PropVal::Item(i(cx, a)?),
            PropVal::Getter(a) => PropVal::Getter(f(cx, a)?),
            PropVal::Setter(a) => PropVal::Setter(f(cx, a)?),
            PropVal::Method(a) => PropVal::Method(f(cx, a)?),
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TCallee<I = Ident> {
    Val(I),
    Member { func: I, member: I },
    PrivateMember { func: I, member: Private },
    Import,
    Super,
    // Static(Ident),
}
impl<I> TCallee<I> {
    pub fn as_ref(&self) -> TCallee<&I> {
        match self {
            TCallee::Val(a) => TCallee::Val(a),
            TCallee::Member { func: r#fn, member } => TCallee::Member { func: r#fn, member },
            TCallee::PrivateMember { func: r#fn, member } => TCallee::PrivateMember {
                func: r#fn,
                member: member.clone(),
            },
            TCallee::Import => TCallee::Import,
            TCallee::Super => TCallee::Super,
            // TCallee::Static(a) => TCallee::Static(a.clone()),
        }
    }
    pub fn as_mut(&mut self) -> TCallee<&mut I> {
        match self {
            TCallee::Val(a) => TCallee::Val(a),
            TCallee::Member { func: r#fn, member } => TCallee::Member { func: r#fn, member },
            TCallee::PrivateMember { func: r#fn, member } => TCallee::PrivateMember {
                func: r#fn,
                member: member.clone(),
            },
            TCallee::Import => TCallee::Import,
            TCallee::Super => TCallee::Super,
            // TCallee::Static(a) => TCallee::Static(a.clone()),
        }
    }
    pub fn map<J: Ord, E>(self, f: &mut impl FnMut(I) -> Result<J, E>) -> Result<TCallee<J>, E> {
        Ok(match self {
            TCallee::Val(a) => TCallee::Val(f(a)?),
            TCallee::Member { func: r#fn, member } => TCallee::Member {
                func: f(r#fn)?,
                member: f(member)?,
            },
            TCallee::PrivateMember { func: r#fn, member } => TCallee::PrivateMember {
                func: f(r#fn)?,
                member,
            },
            TCallee::Import => TCallee::Import,
            TCallee::Super => TCallee::Super,
            // TCallee::Static(a) => TCallee::Static(a),
        })
    }
}

pub fn inlinable<I: Clone, F>(d: &Item<I, F>, tcfg: &(dyn ItemGetter<I, F> + '_)) -> bool {
    match d {
        Item::Asm { value }
            if match value {
                Asm::OrZero(value) => tcfg.get_item(value.clone()).is_some(),
                _ => todo!(),
            } =>
        {
            true
        }
        Item::Lit { lit } => true,
        Item::Un { arg, op }
            if !matches!(op, UnaryOp::Delete) && tcfg.get_item(arg.clone()).is_some() =>
        {
            true
        }
        _ => false,
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Item<I = Ident, F = TFunc> {
    Just {
        id: I,
    },
    Bin {
        left: I,
        right: I,
        op: BinaryOp,
    },
    Un {
        arg: I,
        op: UnaryOp,
    },
    Mem {
        obj: I,
        mem: I,
    },
    PrivateMem {
        obj: I,
        mem: Private,
    },
    HasPrivateMem {
        obj: I,
        mem: Private,
    },
    Func {
        func: F,
        arrow: bool,
    },
    Lit {
        lit: Lit,
    },
    Call {
        callee: TCallee<I>,
        args: Vec<I>,
    },
    New {
        class: I,
        args: Vec<I>,
    },
    Obj {
        members: Vec<(PropKey<I>, PropVal<I, F>)>,
    },
    Class {
        superclass: Option<I>,
        members: Vec<(MemberFlags, PropKey<I>, PropVal<Option<I>, F>)>,
        constructor: Option<F>,
    },
    Arr {
        members: Vec<I>,
    },
    Yield {
        value: Option<I>,
        delegate: bool,
    },
    Await {
        value: I,
    },
    Asm {
        value: Asm<I>,
    },
    Undef,
    This,
    Select {
        cond: I,
        then: I,
        otherwise: I,
    },
    // Intrinsic {
    //     value: Native<I>,
    // },
}
impl<I> Item<I> {
    pub fn map<J: Ord, E>(self, f: &mut (dyn FnMut(I) -> Result<J, E> + '_)) -> Result<Item<J>, E> {
        self.map2(f, &mut |a, b| a(b), &mut |_, b| Ok(b))
    }
}
impl<I, F> Item<I, F> {
    pub fn as_ref(&self) -> Item<&I, &F> {
        match self {
            Item::Just { id } => Item::Just { id },
            Item::Bin { left, right, op } => Item::Bin {
                left,
                right,
                op: *op,
            },
            Item::Un { arg, op } => Item::Un { arg, op: *op },
            Item::Mem { obj, mem } => Item::Mem { obj, mem },
            Item::PrivateMem { obj, mem } => Item::PrivateMem {
                obj,
                mem: mem.clone(),
            },
            Item::HasPrivateMem { obj, mem } => Item::HasPrivateMem {
                obj,
                mem: mem.clone(),
            },
            Item::Func { func, arrow } => Item::Func {
                func,
                arrow: *arrow,
            },
            Item::Lit { lit } => Item::Lit { lit: lit.clone() },
            Item::Call { callee, args } => Item::Call {
                callee: callee.as_ref(),
                args: args.iter().collect(),
            },
            Item::New { class, args } => Item::New {
                class,
                args: args.iter().collect(),
            },
            Item::Obj { members } => Item::Obj {
                members: members
                    .iter()
                    .map(|(a, b)| (a.as_ref(), b.as_ref()))
                    .collect(),
            },
            Item::Arr { members } => Item::Arr {
                members: members.iter().collect(),
            },
            Item::Yield { value, delegate } => Item::Yield {
                value: value.as_ref(),
                delegate: *delegate,
            },
            Item::Await { value } => Item::Await { value },
            Item::Asm { value } => Item::Asm {
                value: value.as_ref(),
            },
            Item::Undef => Item::Undef,
            Item::This => Item::This,
            Item::Class {
                superclass,
                members,
                constructor,
            } => Item::Class {
                superclass: superclass.as_ref(),
                constructor: constructor.as_ref(),
                members: members
                    .iter()
                    .map(|(a, b, c)| {
                        (
                            *a,
                            b.as_ref(),
                            c.as_ref()
                                .map(
                                    &mut (),
                                    &mut |cx, a: &Option<I>| Ok::<_, Infallible>(a.as_ref()),
                                    &mut |cx, b| Ok(b),
                                )
                                .unwrap(),
                        )
                    })
                    .collect(),
            },
            Item::Select {
                cond,
                then,
                otherwise,
            } => Item::Select {
                cond,
                then,
                otherwise,
            },
        }
    }
    pub fn as_mut(&mut self) -> Item<&mut I, &mut F> {
        match self {
            Item::Select {
                cond,
                then,
                otherwise,
            } => Item::Select {
                cond,
                then,
                otherwise,
            },
            Item::Just { id } => Item::Just { id },
            Item::Bin { left, right, op } => Item::Bin {
                left,
                right,
                op: *op,
            },
            Item::Un { arg, op } => Item::Un { arg, op: *op },
            Item::Mem { obj, mem } => Item::Mem { obj, mem },
            Item::PrivateMem { obj, mem } => Item::PrivateMem {
                obj,
                mem: mem.clone(),
            },
            Item::HasPrivateMem { obj, mem } => Item::HasPrivateMem {
                obj,
                mem: mem.clone(),
            },
            Item::Func { func, arrow } => Item::Func {
                func,
                arrow: *arrow,
            },
            Item::Lit { lit } => Item::Lit { lit: lit.clone() },
            Item::Call { callee, args } => Item::Call {
                callee: callee.as_mut(),
                args: args.iter_mut().collect(),
            },
            Item::New { class, args } => Item::New {
                class,
                args: args.iter_mut().collect(),
            },
            Item::Obj { members } => Item::Obj {
                members: members
                    .iter_mut()
                    .map(|(a, b)| (a.as_mut(), b.as_mut()))
                    .collect(),
            },
            Item::Arr { members } => Item::Arr {
                members: members.iter_mut().collect(),
            },
            Item::Yield { value, delegate } => Item::Yield {
                value: value.as_mut(),
                delegate: *delegate,
            },
            Item::Await { value } => Item::Await { value },
            Item::Asm { value } => Item::Asm {
                value: value.as_mut(),
            },
            Item::Undef => Item::Undef,
            Item::This => Item::This,
            Item::Class {
                superclass,
                members,
                constructor,
            } => Item::Class {
                superclass: superclass.as_mut(),
                constructor: constructor.as_mut(),
                members: members
                    .iter_mut()
                    .map(|(a, b, c)| {
                        (
                            *a,
                            b.as_mut(),
                            c.as_mut()
                                .map(
                                    &mut (),
                                    &mut |cx, a| Ok::<_, Infallible>(a.as_mut()),
                                    &mut |cx, b| Ok(b),
                                )
                                .unwrap(),
                        )
                    })
                    .collect(),
            },
            // Item::Intrinsic { value } => Item::Intrinsic {
            //     value: value.as_mut(),
            // },
        }
    }
    pub fn map2<J: Ord, G, E, C: ?Sized>(
        self,
        cx: &mut C,
        f: &mut (dyn FnMut(&mut C, I) -> Result<J, E> + '_),
        g: &mut (dyn FnMut(&mut C, F) -> Result<G, E> + '_),
    ) -> Result<Item<J, G>, E> {
        Ok(match self {
            Item::Select {
                cond,
                then,
                otherwise,
            } => Item::Select {
                cond: f(cx, cond)?,
                then: f(cx, then)?,
                otherwise: f(cx, otherwise)?,
            },
            Item::Just { id } => Item::Just { id: f(cx, id)? },
            Item::Bin { left, right, op } => Item::Bin {
                left: f(cx, left)?,
                right: f(cx, right)?,
                op,
            },
            Item::Un { arg, op } => Item::Un {
                arg: f(cx, arg)?,
                op,
            },
            Item::Mem { obj, mem } => Item::Mem {
                obj: f(cx, obj)?,
                mem: f(cx, mem)?,
            },
            Item::PrivateMem { obj, mem } => Item::PrivateMem {
                obj: f(cx, obj)?,
                mem,
            },
            Item::HasPrivateMem { obj, mem } => Item::HasPrivateMem {
                obj: f(cx, obj)?,
                mem,
            },
            Item::Func { func, arrow } => Item::Func {
                func: g(cx, func)?,
                arrow,
            },
            Item::Lit { lit } => Item::Lit { lit },
            Item::Call { callee, args } => Item::Call {
                callee: callee.map(&mut |a| f(cx, a))?,
                args: args
                    .into_iter()
                    .map(|a| f(cx, a))
                    .collect::<Result<Vec<J>, E>>()?,
            },
            Item::New { class, args } => Item::New {
                class: f(cx, class)?,
                args: args
                    .into_iter()
                    .map(|a| f(cx, a))
                    .collect::<Result<Vec<J>, E>>()?,
            },
            Item::Obj { members } => Item::Obj {
                members: members
                    .into_iter()
                    .map(|(a, b)| Ok((a.map(&mut |a| f(cx, a))?, b.map(cx, f, g)?)))
                    .collect::<Result<_, E>>()?,
            },
            Item::Arr { members } => Item::Arr {
                members: members
                    .into_iter()
                    .map(|a| f(cx, a))
                    .collect::<Result<_, E>>()?,
            },
            Item::Yield { value, delegate } => Item::Yield {
                value: match value {
                    None => None,
                    Some(a) => Some(f(cx, a)?),
                },
                delegate: delegate,
            },
            Item::Await { value } => Item::Await {
                value: f(cx, value)?,
            },
            Item::Undef => Item::Undef,
            Item::Asm { value } => Item::Asm {
                value: value.map(&mut |a| f(cx, a))?,
            },
            Item::This => Item::This,
            Item::Class {
                superclass,
                members,
                constructor,
            } => Item::Class {
                superclass: match superclass {
                    None => None,
                    Some(a) => Some(f(cx, a)?),
                },
                constructor: match constructor {
                    None => None,
                    Some(a) => Some(g(cx, a)?),
                },
                members: members
                    .into_iter()
                    .map(|(a, b, c)| {
                        Ok((
                            a,
                            b.map(&mut |a| f(cx, a))?,
                            c.map(
                                cx,
                                &mut |cx, a: Option<I>| {
                                    Ok(match a {
                                        None => None,
                                        Some(v) => Some(f(cx, v)?),
                                    })
                                },
                                g,
                            )?,
                        ))
                    })
                    .collect::<Result<_, E>>()?,
            },
            // Item::Intrinsic { value } => Item::Intrinsic {
            //     value: value.map(&mut |a| f(cx, a))?,
            // },
        })
    }
    pub fn funcs<'a>(&'a self) -> Box<dyn Iterator<Item = &'a F> + 'a> {
        match self {
            Item::Func { func, arrow } => Box::new(once(func)),
            Item::Obj { members } => Box::new(members.iter().filter_map(|m| match &m.1 {
                PropVal::Getter(f) | PropVal::Setter(f) | PropVal::Method(f) => Some(f),
                _ => None,
            })),
            Item::Class {
                superclass,
                members,
                constructor,
            } => Box::new(
                members
                    .iter()
                    .filter_map(|m| match &m.2 {
                        PropVal::Getter(f) | PropVal::Setter(f) | PropVal::Method(f) => Some(f),
                        _ => None,
                    })
                    .chain(constructor.iter()),
            ),
            _ => Box::new(empty()),
        }
    }
    pub fn refs<'a>(&'a self) -> Box<dyn Iterator<Item = &'a I> + 'a> {
        use crate as swc_tac;
        match self {
            swc_tac::Item::Just { id } => Box::new(once(id)),
            swc_tac::Item::Bin { left, right, op } => Box::new([left, right].into_iter()),
            swc_tac::Item::Un { arg, op } => Box::new(once(arg)),
            swc_tac::Item::Mem { obj, mem } => Box::new([obj, mem].into_iter()),
            Item::PrivateMem { obj, mem } | Item::HasPrivateMem { obj, mem } => Box::new(once(obj)),
            swc_tac::Item::Func { func, arrow } => Box::new(empty()),
            swc_tac::Item::Lit { lit } => Box::new(empty()),
            swc_tac::Item::Call { callee, args } => Box::new(
                match callee {
                    swc_tac::TCallee::Val(a) | TCallee::PrivateMember { func: a, member: _ } => {
                        vec![a]
                    }
                    swc_tac::TCallee::Member { func: r#fn, member } => vec![r#fn, member],
                    TCallee::Import | TCallee::Super => vec![], // swc_tac::TCallee::Static(_) => vec![],
                }
                .into_iter()
                .chain(args.iter()),
            ),
            Item::New { class, args } => Box::new(args.iter().chain([class])),
            swc_tac::Item::Obj { members } => Box::new(members.iter().flat_map(|m| {
                let v: Box<dyn Iterator<Item = &I> + '_> = match &m.1 {
                    PropVal::Getter(a) | PropVal::Setter(a) | PropVal::Method(a) => {
                        Box::new(empty())
                    }
                    PropVal::Item(i) => Box::new(once(i)),
                };
                let w: Box<dyn Iterator<Item = &I> + '_> = match &m.0 {
                    swc_tac::PropKey::Lit(_) => Box::new(empty()),
                    swc_tac::PropKey::Computed(c) => Box::new(once(c)),
                };
                v.chain(w)
            })),
            swc_tac::Item::Arr { members } => Box::new(members.iter()),
            swc_tac::Item::Yield { value, delegate } => Box::new(value.iter()),
            swc_tac::Item::Await { value } => Box::new(once(value)),
            swc_tac::Item::Undef | Item::This => Box::new(empty()),
            Item::Asm { value } => Box::new(value.refs()),
            Item::Class {
                superclass,
                members,
                constructor,
            } => Box::new(superclass.iter().chain(members.iter().flat_map(|m| {
                let v: Box<dyn Iterator<Item = &I> + '_> = match &m.2 {
                    PropVal::Getter(a) | PropVal::Setter(a) | PropVal::Method(a) => {
                        Box::new(empty())
                    }
                    PropVal::Item(i) => Box::new(i.iter()),
                };
                let w: Box<dyn Iterator<Item = &I> + '_> = match &m.1 {
                    swc_tac::PropKey::Lit(_) => Box::new(empty()),
                    swc_tac::PropKey::Computed(c) => Box::new(once(c)),
                };
                v.chain(w)
            }))),
            Item::Select {
                cond,
                then,
                otherwise,
            } => Box::new([cond, then, otherwise].into_iter()),
            // Item::Intrinsic { value } => {
            //     let mut v = Vec::default();
            //     value
            //         .as_ref()
            //         .map(&mut |a| Ok::<_, Infallible>(v.push(a)))
            //         .unwrap();
            //     Box::new(v.into_iter())
            // }
        }
    }
    pub fn refs_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut I> + 'a> {
        use crate as swc_tac;
        match self {
            Item::Select {
                cond,
                then,
                otherwise,
            } => Box::new([cond, then, otherwise].into_iter()),
            swc_tac::Item::Just { id } => Box::new(once(id)),
            swc_tac::Item::Bin { left, right, op } => Box::new([left, right].into_iter()),
            swc_tac::Item::Un { arg, op } => Box::new(once(arg)),
            swc_tac::Item::Mem { obj, mem } => Box::new([obj, mem].into_iter()),
            Item::PrivateMem { obj, mem } | Item::HasPrivateMem { obj, mem } => Box::new(once(obj)),
            swc_tac::Item::Func { func, arrow } => Box::new(empty()),
            swc_tac::Item::Lit { lit } => Box::new(empty()),
            swc_tac::Item::Call { callee, args } => Box::new(
                match callee {
                    swc_tac::TCallee::Val(a) | TCallee::PrivateMember { func: a, member: _ } => {
                        vec![a]
                    }
                    swc_tac::TCallee::Member { func: r#fn, member } => vec![r#fn, member],
                    TCallee::Import | TCallee::Super => vec![], // swc_tac::TCallee::Static(_) => vec![],
                }
                .into_iter()
                .chain(args.iter_mut()),
            ),
            Item::New { class, args } => Box::new(args.iter_mut().chain([class])),
            swc_tac::Item::Obj { members } => Box::new(members.iter_mut().flat_map(|m| {
                let v: Box<dyn Iterator<Item = &mut I> + '_> = match &mut m.1 {
                    PropVal::Getter(a) | PropVal::Setter(a) | PropVal::Method(a) => {
                        Box::new(empty())
                    }
                    PropVal::Item(i) => Box::new(once(i)),
                };
                let w: Box<dyn Iterator<Item = &mut I> + '_> = match &mut m.0 {
                    swc_tac::PropKey::Lit(_) => Box::new(empty()),
                    swc_tac::PropKey::Computed(c) => Box::new(once(c)),
                };
                v.chain(w)
            })),
            swc_tac::Item::Arr { members } => Box::new(members.iter_mut()),
            swc_tac::Item::Yield { value, delegate } => Box::new(value.iter_mut()),
            swc_tac::Item::Await { value } => Box::new(once(value)),
            swc_tac::Item::Undef | Item::This => Box::new(empty()),
            Item::Asm { value } => Box::new(value.refs_mut()),
            Item::Class {
                superclass,
                members,
                constructor,
            } => Box::new(
                superclass
                    .iter_mut()
                    .chain(members.iter_mut().flat_map(|m| {
                        let v: Box<dyn Iterator<Item = &mut I> + '_> = match &mut m.2 {
                            PropVal::Getter(a) | PropVal::Setter(a) | PropVal::Method(a) => {
                                Box::new(empty())
                            }
                            PropVal::Item(i) => Box::new(i.iter_mut()),
                        };
                        let w: Box<dyn Iterator<Item = &mut I> + '_> = match &mut m.1 {
                            swc_tac::PropKey::Lit(_) => Box::new(empty()),
                            swc_tac::PropKey::Computed(c) => Box::new(once(c)),
                        };
                        v.chain(w)
                    })),
            ),
            // Item::Intrinsic { value } => {
            //     let mut v = Vec::default();
            //     value
            //         .as_mut()
            //         .map(&mut |a| Ok::<_, Infallible>(v.push(a)))
            //         .unwrap();
            //     Box::new(v.into_iter())
            // }
        }
    }
}
enum Frame {
    Assign(AssignTarget, AssignOp),
    Member(MemberProp),
    Member2(Expr, Expr),
}
// #[derive(Default)]
