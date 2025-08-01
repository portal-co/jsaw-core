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

pub mod lam;
pub mod prepa;
pub mod rew;
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
impl TFunc {
    pub fn try_from_with_mapper(value: &Func, mapper: Mapper<'_>) -> anyhow::Result<Self> {
        let mut cfg = TCfg::default();
        let entry = Trans {
            map: BTreeMap::new(),
            ret_to: None,
            recatch: TCatch::Throw,
            this: None,
            mapper,
        }
        .trans(&value.cfg, &mut cfg, value.entry)?;
        cfg.ts_retty = value.cfg.ts_retty.clone();
        cfg.generics = value.cfg.generics.clone();
        let mut ts_params = vec![];
        let params = value
            .params
            .iter()
            .filter_map(|x| match &x.pat {
                Pat::Ident(i) => {
                    ts_params.push(i.type_ann.as_ref().map(|a| (&*a.type_ann).clone()));
                    Some(i.id.clone().into())
                }
                _ => None,
            })
            .collect::<Vec<Ident>>();
        Ok(Self {
            cfg,
            entry,
            params,
            is_generator: value.is_generator,
            is_async: value.is_async,
            ts_params,
        })
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
pub trait ItemGetter<I = Ident, F = TFunc> {
    fn get_item(&self, i: I) -> Option<&Item<I, F>>;
}
impl ItemGetter for TCfg {
    fn get_item(&self, i: (Atom, SyntaxContext)) -> Option<&Item<(Atom, SyntaxContext), TFunc>> {
        self.def(LId::Id { id: i })
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
#[non_exhaustive]
pub struct Trans<'a> {
    pub map: BTreeMap<Id<Block>, Id<TBlock>>,
    pub ret_to: Option<(Ident, Id<TBlock>)>,
    pub recatch: TCatch,
    pub this: Option<Ident>,
    pub mapper: Mapper<'a>,
}
impl Trans<'_> {
    pub fn trans(&mut self, i: &Cfg, o: &mut TCfg, b: Id<Block>) -> anyhow::Result<Id<TBlock>> {
        loop {
            if let Some(a) = self.map.get(&b) {
                return Ok(*a);
            }
            let t = o.blocks.alloc(TBlock {
                stmts: vec![],
                post: TPostecedent {
                    catch: self.recatch.clone(),
                    term: Default::default(),
                    orig_span: i.blocks[b].end.orig_span.clone(),
                },
            });
            self.map.insert(b, t);
            if let Catch::Jump { pat, k } = &i.blocks[b].end.catch {
                match pat {
                    Pat::Ident(id) => {
                        let k = self.trans(i, o, *k)?;
                        o.blocks[t].post.catch = TCatch::Jump {
                            pat: id.id.clone().into(),
                            k,
                        };
                    }
                    _ => anyhow::bail!("todo: {}:{}", file!(), line!()),
                }
            }
            let mut t = t;
            for s in i.blocks[b].stmts.iter() {
                t = self.stmt(i, o, b, t, s)?;
            }
            let term = match &i.blocks[b].end.term {
                swc_cfg::Term::Return(expr) => match self.ret_to.clone() {
                    None => match expr {
                        None => TTerm::Return(None),
                        Some(a) => {
                            let c;
                            (c, t) = self.expr(i, o, b, t, a)?;
                            TTerm::Return(Some(c))
                        }
                    },
                    Some((i2, b2)) => {
                        if let Some(a) = expr {
                            let c;
                            (c, t) = self.expr(i, o, b, t, a)?;
                            o.blocks[t].stmts.push(TStmt {
                                left: LId::Id { id: i2.clone() },
                                flags: Default::default(),
                                right: Item::Just { id: c },
                                span: i.blocks[b]
                                    .end
                                    .orig_span
                                    .clone()
                                    .unwrap_or_else(|| Span::dummy_with_cmt()),
                            });
                        }
                        TTerm::Jmp(b2)
                    }
                },
                swc_cfg::Term::Throw(expr) => {
                    let c;
                    (c, t) = self.expr(i, o, b, t, expr)?;
                    TTerm::Throw(c)
                }
                swc_cfg::Term::Jmp(id) => TTerm::Jmp(self.trans(i, o, *id)?),
                swc_cfg::Term::CondJmp {
                    cond,
                    if_true,
                    if_false,
                } => {
                    let c;
                    (c, t) = self.expr(i, o, b, t, cond)?;
                    TTerm::CondJmp {
                        cond: c,
                        if_true: self.trans(i, o, *if_true)?,
                        if_false: self.trans(i, o, *if_false)?,
                    }
                }
                swc_cfg::Term::Switch { x, blocks, default } => {
                    let y;
                    (y, t) = self.expr(i, o, b, t, x)?;
                    let mut m2 = HashMap::new();
                    for (a, b2) in blocks.iter() {
                        let b2 = self.trans(i, o, *b2)?;
                        let c;
                        (c, t) = self.expr(i, o, b, t, a)?;
                        m2.insert(c, b2);
                    }
                    TTerm::Switch {
                        x: y,
                        blocks: m2,
                        default: self.trans(i, o, *default)?,
                    }
                }
                swc_cfg::Term::Default => TTerm::Default,
            };
            o.blocks[t].post.term = term;
        }
    }
    pub fn stmt(
        &mut self,
        i: &Cfg,
        o: &mut TCfg,
        b: Id<Block>,
        mut t: Id<TBlock>,
        s: &Stmt,
    ) -> anyhow::Result<Id<TBlock>> {
        match s {
            Stmt::Expr(e) => {
                (_, t) = self.expr(i, o, b, t, &e.expr)?;
                return Ok(t);
            }
            Stmt::Empty(_) => return Ok(t),
            Stmt::Decl(d) => match d {
                swc_ecma_ast::Decl::Class(f) => {
                    let c;
                    (c, t) = self.class(i, o, b, t, &f.class)?;
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id {
                            id: f.ident.clone().into(),
                        },
                        flags: Default::default(),
                        right: Item::Just { id: c },
                        span: f.span(),
                    });
                    o.decls.insert(f.ident.clone().into());
                    return Ok(t);
                }
                swc_ecma_ast::Decl::Fn(f) => {
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id {
                            id: f.ident.clone().into(),
                        },
                        flags: Default::default(),
                        right: Item::Func {
                            func: f.function.as_ref().clone().try_into()?,
                            arrow: false,
                        },
                        span: f.span(),
                    });
                    o.decls.insert(f.ident.clone().into());
                    return Ok(t);
                }
                swc_ecma_ast::Decl::Var(var_decl) => {
                    for var_decl in var_decl.decls.iter() {
                        if let Some(e) = &var_decl.init {
                            match &var_decl.name {
                                Pat::Ident(i2) => {
                                    let f;
                                    (f, t) = self.expr(i, o, b, t, e)?;
                                    o.blocks[t].stmts.push(TStmt {
                                        left: LId::Id {
                                            id: i2.id.clone().into(),
                                        },
                                        flags: Default::default(),
                                        right: Item::Just { id: f },
                                        span: e.span(),
                                    });
                                    o.decls.insert(i2.id.clone().into());
                                    if let Some(a) = i2.type_ann.as_ref().cloned() {
                                        o.type_annotations
                                            .insert(i2.id.clone().into(), *a.type_ann);
                                    }
                                }
                                _ => anyhow::bail!("todo: {}:{}", file!(), line!()),
                            }
                        }
                    }
                    return Ok(t);
                }
                swc_ecma_ast::Decl::Using(using_decl) => todo!(),
                swc_ecma_ast::Decl::TsInterface(ts_interface_decl) => todo!(),
                swc_ecma_ast::Decl::TsTypeAlias(ts_type_alias_decl) => todo!(),
                swc_ecma_ast::Decl::TsEnum(ts_enum_decl) => todo!(),
                swc_ecma_ast::Decl::TsModule(ts_module_decl) => todo!(),
            },
            _ => anyhow::bail!("todo: {}:{}", file!(), line!()),
        }
    }
    pub fn member_expr(
        &mut self,
        i: &Cfg,
        o: &mut TCfg,
        b: Id<Block>,
        mut t: Id<TBlock>,
        s: &MemberExpr,
    ) -> anyhow::Result<(Ident, Id<TBlock>)> {
        let obj;
        (obj, t) = self.expr(i, o, b, t, &s.obj)?;
        self.member_prop(i, o, b, t, &s.prop, obj)
    }
    pub fn member_prop(
        &mut self,
        i: &Cfg,
        o: &mut TCfg,
        b: Id<Block>,
        mut t: Id<TBlock>,
        s: &MemberProp,
        obj: Ident,
    ) -> anyhow::Result<(Ident, Id<TBlock>)> {
        let i = match s {
            MemberProp::PrivateName(p) => Item::PrivateMem {
                obj,
                mem: Private {
                    sym: p.name.clone(),
                    ctxt: self
                        .mapper
                        .privates
                        .get(&p.name)
                        .context("in getting the private")?
                        .clone(),
                    span: p.span,
                },
            },
            _ => {
                let mem;
                // let e;
                (mem, t) = self.expr(i, o, b, t, &imp(s.clone()))?;
                Item::Mem { obj, mem }
            }
        };
        let v = o.regs.alloc(());
        o.blocks[t].stmts.push(TStmt {
            left: LId::Id { id: v.clone() },
            flags: ValFlags::SSA_LIKE,
            right: i,
            span: s.span(),
        });
        o.decls.insert(v.clone());
        Ok((v, t))
    }
    pub fn class(
        &mut self,
        i: &Cfg,
        o: &mut TCfg,
        b: Id<Block>,
        mut t: Id<TBlock>,
        s: &Class,
    ) -> anyhow::Result<(Ident, Id<TBlock>)> {
        let superclass = match &s.super_class {
            None => None,
            Some(a) => Some({
                let b2;
                (b2, t) = self.expr(i, o, b, t, a)?;
                b2
            }),
        };
        macro_rules! prop_name {
            ( $w:expr , $v:expr => $a:expr) => {
                match $v {
                    v => match $w {
                        w => match $a {
                            swc_ecma_ast::PropName::Ident(ident_name) => (
                                w,
                                PropKey::Lit((ident_name.sym.clone(), Default::default())),
                                v,
                            ),
                            swc_ecma_ast::PropName::Str(s) => {
                                ((w, PropKey::Lit((s.value.clone(), Default::default())), v))
                            }
                            swc_ecma_ast::PropName::Num(number) => {
                                anyhow::bail!("todo: {}:{}", file!(), line!())
                            }
                            swc_ecma_ast::PropName::Computed(computed_prop_name) => {
                                let w2;
                                (w2, t) = self.expr(i, o, b, t, &computed_prop_name.expr)?;
                                ((w, PropKey::Computed(w2), v))
                            }
                            swc_ecma_ast::PropName::BigInt(big_int) => {
                                anyhow::bail!("todo: {}:{}", file!(), line!())
                            }
                        },
                    },
                }
            };
        }
        let mut members: Vec<(
            MemberFlags,
            PropKey,
            PropVal<Option<(Atom, swc_common::SyntaxContext)>, TFunc>,
        )> = Default::default();
        let mut constructor: Option<TFunc> = Default::default();
        let mut privates = self.mapper.privates.clone();
        let ctx = SyntaxContext::empty().apply_mark(Mark::new());
        for m in s.body.iter() {
            match m {
                ClassMember::PrivateMethod(m) => {
                    privates.insert(m.key.name.clone(), ctx);
                }
                ClassMember::PrivateProp(m) => {
                    privates.insert(m.key.name.clone(), ctx);
                }
                _ => {}
            }
        }
        let mut mapper = self.mapper.clone();
        let mut mapper = mapper.bud();
        mapper.privates = &privates;
        for m in s.body.iter() {
            match m {
                ClassMember::ClassProp(p) => {
                    members.push(
                        prop_name!(if p.is_static{MemberFlags::STATIC}else{MemberFlags::empty()},PropVal::Item( match p.value.as_ref(){
                                    None => None,
                                    Some(a) => Some({
                            let b2;
                            (b2, t) = self.expr(i, o, b, t, a)?;
                            b2
                        }),
                    }) => &p.key),
                    );
                }
                ClassMember::Constructor(c) => {
                    constructor = Some(TFunc::try_from_with_mapper(
                        &Function {
                            body: c.body.clone(),
                            params: c
                                .params
                                .iter()
                                .filter_map(|a| a.as_param())
                                .cloned()
                                .collect(),
                            is_async: false,
                            is_generator: false,
                            span: c.span,
                            decorators: vec![],
                            ctxt: Default::default(),
                            type_params: None,
                            return_type: None,
                        }
                        .try_into()?,
                        mapper.bud(),
                    )?)
                }
                ClassMember::Method(c) => {
                    let f = TFunc::try_from_with_mapper(
                        &(&*c.function).clone().try_into()?,
                        mapper.bud(),
                    )?;
                    members.push(prop_name!(if c.is_static{MemberFlags::STATIC}else{MemberFlags::empty()}, match &c.kind{
                        swc_ecma_ast::MethodKind::Method => PropVal::Method(f),
                        swc_ecma_ast::MethodKind::Getter => PropVal::Getter(f),
                        swc_ecma_ast::MethodKind::Setter => PropVal::Setter(f),
                    }=> &c.key));
                }
                ClassMember::PrivateProp(p) => {
                    members.push((
                        if p.is_static {
                            MemberFlags::STATIC
                        } else {
                            MemberFlags::empty()
                        } | MemberFlags::PRIVATE,
                        PropKey::Lit((
                            p.key.name.clone(),
                            privates
                                .get(&p.key.name)
                                .context("in getting the private")?
                                .clone(),
                        )),
                        PropVal::Item(match p.value.as_ref() {
                            None => None,
                            Some(a) => Some({
                                let b2;
                                (b2, t) = self.expr(i, o, b, t, a)?;
                                b2
                            }),
                        }),
                    ));
                }
                ClassMember::PrivateMethod(p) => {
                    let f = TFunc::try_from_with_mapper(
                        &(&*p.function).clone().try_into()?,
                        mapper.bud(),
                    )?;
                    let x = match &p.kind {
                        swc_ecma_ast::MethodKind::Method => PropVal::Method(f),
                        swc_ecma_ast::MethodKind::Getter => PropVal::Getter(f),
                        swc_ecma_ast::MethodKind::Setter => PropVal::Setter(f),
                    };
                    members.push((
                        if p.is_static {
                            MemberFlags::STATIC
                        } else {
                            MemberFlags::empty()
                        } | MemberFlags::PRIVATE,
                        PropKey::Lit((
                            p.key.name.clone(),
                            privates
                                .get(&p.key.name)
                                .context("in getting the private")?
                                .clone(),
                        )),
                        x,
                    ));
                }
                _ => anyhow::bail!("todo: {}:{}", file!(), line!()),
            }
        }
        let tmp = o.regs.alloc(());
        o.blocks[t].stmts.push(TStmt {
            left: LId::Id { id: tmp.clone() },
            flags: Default::default(),
            right: Item::Class {
                superclass,
                members,
                constructor,
            },
            span: s.span(),
        });
        o.decls.insert(tmp.clone());
        Ok((tmp, t))
    }
    fn assign(
        &mut self,
        i: &Cfg,
        o: &mut TCfg,
        b: Id<Block>,
        mut t: Id<TBlock>,
        tgt: &AssignTarget,
        op: &AssignOp,
        mut right: Ident,
    ) -> anyhow::Result<(Ident, Id<TBlock>)> {
        match tgt {
            swc_ecma_ast::AssignTarget::Simple(simple_assign_target) => match &simple_assign_target
            {
                SimpleAssignTarget::Ident(i) => {
                    let item = match op.clone().to_update() {
                        None => Item::Just { id: right.clone() },
                        Some(a) => Item::Bin {
                            left: right.clone(),
                            right: i.id.clone().into(),
                            op: a,
                        },
                    };
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id {
                            id: i.id.clone().into(),
                        },
                        flags: Default::default(),
                        right: item,
                        span: i.span(),
                    });
                    // right = i.id.clone().into();
                }
                SimpleAssignTarget::Member(m) => {
                    let obj;
                    let mem;
                    let mut priv_ = None;
                    let mut private = false;
                    let e;
                    (obj, t) = self.expr(i, o, b, t, &m.obj)?;
                    'a: {
                        (mem, t) = self.expr(
                            i,
                            o,
                            b,
                            t,
                            match &m.prop {
                                swc_ecma_ast::MemberProp::Ident(ident_name) => {
                                    e = Expr::Ident(swc_ecma_ast::Ident::new(
                                        ident_name.sym.clone(),
                                        ident_name.span,
                                        Default::default(),
                                    ));
                                    &e
                                }
                                swc_ecma_ast::MemberProp::PrivateName(private_name) => {
                                    private = true;
                                    priv_ = Some(Private {
                                        sym: private_name.name.clone(),
                                        ctxt: self
                                            .mapper
                                            .privates
                                            .get(&private_name.name)
                                            .context("in getting the private")?
                                            .clone(),
                                        span: private_name.span,
                                    });
                                    mem = match priv_.clone().unwrap() {
                                        Private {
                                            sym: a, ctxt: b, ..
                                        } => (a, b),
                                    };
                                    break 'a;
                                }
                                swc_ecma_ast::MemberProp::Computed(computed_prop_name) => {
                                    &computed_prop_name.expr
                                }
                            },
                        )?;
                    }
                    let item = match op.clone().to_update() {
                        None => Item::Just { id: right.clone() },
                        Some(a) => {
                            let id = o.regs.alloc(());
                            o.blocks[t].stmts.push(TStmt {
                                left: LId::Id { id: id.clone() },
                                flags: ValFlags::SSA_LIKE,
                                right: if private {
                                    Item::PrivateMem {
                                        obj: obj.clone(),
                                        mem: priv_.as_ref().unwrap().clone(),
                                    }
                                } else {
                                    Item::Mem {
                                        obj: obj.clone(),
                                        mem: mem.clone(),
                                    }
                                },
                                span: m.span(),
                            });
                            Item::Bin {
                                left: right.clone(),
                                right: id,
                                op: a,
                            }
                        }
                    };
                    o.blocks[t].stmts.push(TStmt {
                        left: if private {
                            LId::Private {
                                obj: obj.clone(),
                                id: priv_.as_ref().unwrap().clone(),
                            }
                        } else {
                            LId::Member {
                                obj: obj.clone(),
                                mem: [mem.clone()],
                            }
                        },
                        flags: Default::default(),
                        right: item,
                        span: m.span(),
                    });
                    // right = o.regs.alloc(());
                    // o.blocks[t].stmts.push(TStmt {
                    //     left: LId::Id { id: right.clone() },
                    //     flags: ValFlags::SSA_LIKE,
                    //     right: Item::Mem { obj, mem },
                    //     span: m.span(),
                    // });
                    // o.decls.insert(right.clone());
                }
                _ => anyhow::bail!("todo: {}:{}", file!(), line!()),
            },
            swc_ecma_ast::AssignTarget::Pat(assign_target_pat) => match &assign_target_pat {
                _ => anyhow::bail!("todo: {}:{}", file!(), line!()),
            },
        };
        Ok((right, t))
    }
    fn frame(
        &mut self,
        i: &Cfg,
        o: &mut TCfg,
        b: Id<Block>,
        mut t: Id<TBlock>,
        f: Frame,
        s: Ident,
        r: Ident,
    ) -> anyhow::Result<(Ident, Id<TBlock>)> {
        match f {
            Frame::Assign(assign_target, assign_op) => {
                self.assign(i, o, b, t, &assign_target, &assign_op, s)
            }
            Frame::Member(m) => self.member_prop(i, o, b, t, &m, s),
            Frame::Member2(a, b2) => self.member_prop(
                i,
                o,
                b,
                t,
                &MemberProp::Computed(ComputedPropName {
                    span: Span::dummy_with_cmt(),
                    expr: Box::new(Expr::Cond(CondExpr {
                        span: Span::dummy_with_cmt(),
                        test: r.into(),
                        cons: Box::new(a),
                        alt: Box::new(b2),
                    })),
                }),
                s,
            ),
        }
    }
    fn inlinable(&self, x: &Expr) -> bool {
        match x {
            Expr::Fn(_) | Expr::Arrow(_) => true,
            _ => false,
        }
    }
    pub fn expr(
        &mut self,
        i: &Cfg,
        o: &mut TCfg,
        b: Id<Block>,
        mut t: Id<TBlock>,
        s: &Expr,
    ) -> anyhow::Result<(Ident, Id<TBlock>)> {
        // if let Some(i2) = self.import_mapper[ImportMapperReq::Native].as_deref() {
        //     if let Some(n) = s.resolve_natives(i2) {
        //         let arg = n.map(&mut |e| {
        //             let x;
        //             (x, t) = self.expr(i, o, b, t, e)?;
        //             anyhow::Ok(x)
        //         })?;
        //         let tmp = o.regs.alloc(());
        //         o.blocks[t].stmts.push(TStmt {
        //             left: LId::Id { id: tmp.clone() },
        //             flags: ValFlags::SSA_LIKE,
        //             right: Item::Intrinsic { value: arg },
        //             span: s.span(),
        //         });
        //         o.decls.insert(tmp.clone());
        //         return Ok((tmp, t));
        //     }
        // }
        match s {
            Expr::Class(c) => {
                let d;
                (d, t) = self.class(i, o, b, t, &*c.class)?;
                if let Some(n) = c.ident.as_ref() {
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: n.to_id() },
                        flags: Default::default(),
                        right: Item::Just { id: d.clone() },
                        span: n.span(),
                    });
                }
                Ok((d, t))
            }
            Expr::Cond(c) => {
                let v;
                (v, t) = self.expr(i, o, b, t, &c.test)?;
                match o.def(LId::Id { id: v.clone() }) {
                    Some(Item::Lit { lit: Lit::Bool(b2) }) => {
                        let w;
                        (w, t) = self.expr(
                            i,
                            o,
                            b,
                            t,
                            match b2.value {
                                true => &c.cons,
                                false => &c.alt,
                            },
                        )?;
                        return Ok((w, t));
                    }
                    _ => {}
                }
                fn px<'a, 'b>(
                    a: &'a Expr,
                    b: &'b Expr,
                ) -> Option<(Vec<Frame>, &'a Expr, &'b Expr)> {
                    if a.is_pure() && b.is_pure() {
                        Some((vec![], a, b))
                    } else {
                        match (a, b) {
                            (Expr::Assign(a), Expr::Assign(b))
                                if a.left.eq_ignore_span(&b.left)
                                    && a.left.as_simple().is_some_and(|s| s.is_ident())
                                    && a.op == b.op =>
                            {
                                let (mut e, a2, b) = px(&a.right, &b.right)?;
                                e.push(Frame::Assign(a.left.clone(), a.op));
                                Some((e, a2, b))
                            }
                            (Expr::Member(a), Expr::Member(b))
                                if a.prop.eq_ignore_span(&b.prop) =>
                            {
                                let (mut e, a2, b) = px(&a.obj, &b.obj)?;
                                e.push(Frame::Member(a.prop.clone()));
                                Some((e, a2, b))
                            }
                            (Expr::Member(a), Expr::Member(b))
                                if a.prop.is_computed() && b.prop.is_computed() =>
                            {
                                let (mut e, a2, b2) = px(&a.obj, &b.obj)?;
                                e.push(Frame::Member2(
                                    *a.prop.as_computed().unwrap().expr.clone(),
                                    *b.prop.as_computed().unwrap().expr.clone(),
                                ));
                                Some((e, a2, b2))
                            }
                            _ => None,
                        }
                    }
                }
                if let Some((frames, c2, a2)) = px(&c.cons, &c.alt) {
                    let cons;
                    let alt;
                    (cons, t) = self.expr(i, o, b, t, &c2)?;
                    (alt, t) = self.expr(i, o, b, t, &a2)?;
                    let mut tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Select {
                            cond: v.clone(),
                            then: cons,
                            otherwise: alt,
                        },
                        span: c.span(),
                    });
                    o.decls.insert(tmp.clone());
                    for f in frames.into_iter() {
                        (tmp, t) = self.frame(i, o, b, t, f, tmp, v.clone())?;
                    }
                    Ok((tmp, t))
                } else {
                    let then = o.blocks.alloc(TBlock {
                        stmts: vec![],
                        post: TPostecedent {
                            catch: o.blocks[t].post.catch.clone(),
                            term: Default::default(),
                            orig_span: Some(c.span),
                        },
                    });
                    let els = o.blocks.alloc(TBlock {
                        stmts: vec![],
                        post: TPostecedent {
                            catch: o.blocks[t].post.catch.clone(),
                            term: Default::default(),
                            orig_span: Some(c.span),
                        },
                    });
                    let done = o.blocks.alloc(TBlock {
                        stmts: vec![],
                        post: TPostecedent {
                            catch: o.blocks[t].post.catch.clone(),
                            term: Default::default(),
                            orig_span: Some(c.span),
                        },
                    });
                    o.blocks[t].post.term = TTerm::CondJmp {
                        cond: v,
                        if_true: then,
                        if_false: els,
                    };
                    let tmp = o.regs.alloc(());
                    o.decls.insert(tmp.clone());
                    let (a, then) = self.expr(i, o, b, then, &c.cons)?;
                    o.blocks[then].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Just { id: a },
                        span: s.span(),
                    });
                    o.blocks[then].post.term = TTerm::Jmp(done);
                    let (a, els) = self.expr(i, o, b, els, &c.alt)?;
                    o.blocks[els].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Just { id: a },
                        span: s.span(),
                    });
                    o.blocks[els].post.term = TTerm::Jmp(done);
                    return Ok((tmp, done));
                }
            }
            Expr::This(this) => {
                let id = match self.this.clone() {
                    Some(a) => a,
                    None => {
                        let tmp = o.regs.alloc(());
                        o.blocks[t].stmts.push(TStmt {
                            left: LId::Id { id: tmp.clone() },
                            flags: ValFlags::SSA_LIKE,
                            right: Item::This,
                            span: this.span(),
                        });
                        o.decls.insert(tmp.clone());
                        tmp
                    }
                };
                return Ok((id, t));
            }
            Expr::Ident(id) => match self
                .mapper
                .consts
                .as_deref()
                .and_then(|c| c.map.get(&id.to_id()))
            {
                Some(e) if self.inlinable(e) => self.expr(i, o, b, t, &*e.clone()),
                _ => Ok((id.clone().into(), t)),
            },
            Expr::Assign(a) => {
                let mut right;
                (right, t) = self.expr(i, o, b, t, &a.right)?;
                let (right, t) = self.assign(i, o, b, t, &a.left, &a.op, right)?;
                return Ok((right, t));
            }
            Expr::New(n) => {
                let obj;
                (obj, t) = self.expr(i, o, b, t, &n.callee)?;
                let args = n
                    .args
                    .iter()
                    .flatten()
                    .map(|a| {
                        let arg;
                        (arg, t) = self.expr(i, o, b, t, &a.expr)?;
                        anyhow::Ok(arg)
                    })
                    .collect::<anyhow::Result<_>>()?;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::New { class: obj, args },
                    span: n.span(),
                });
                o.decls.insert(tmp.clone());
                return Ok((tmp, t));
            }
            Expr::Call(call) => {
                let c = match &call.callee {
                    Callee::Import(i) => TCallee::Import,
                    Callee::Super(s) => TCallee::Super,
                    Callee::Expr(e) => match e.as_ref() {
                        Expr::Member(m) => {
                            let r#fn;
                            (r#fn, t) = self.expr(i, o, b, t, &m.obj)?;
                            match &m.prop {
                                MemberProp::PrivateName(p) => TCallee::PrivateMember {
                                    func: r#fn,
                                    member: Private {
                                        sym: p.name.clone(),
                                        ctxt: Default::default(),
                                        span: p.span,
                                    },
                                },
                                _ => {
                                    let member;
                                    (member, t) = self.expr(i, o, b, t, &imp(m.prop.clone()))?;
                                    TCallee::Member { func: r#fn, member }
                                }
                            }
                        }
                        // Expr::Fn(f) if f.function.params.len() == call.args.len() => {
                        //     for (p, a) in f.function.params.iter().zip(call.args.iter()) {
                        //         let Pat::Ident(id) = &p.pat else {
                        //             anyhow::bail!("non-simple pattern")
                        //         };
                        //         let arg;
                        //         (arg, t) = self.expr(i, o, b, t, &a.expr)?;
                        //         o.blocks[t].stmts.push(TStmt {
                        //             left: LId::Id { id: id.to_id() },
                        //             flags: Default::default(),
                        //             right: Item::Just { id: arg },
                        //             span: a.span(),
                        //         });
                        //     }
                        //     let tmp = o.regs.alloc(());
                        //     let t2 = o.blocks.alloc(TBlock {
                        //         stmts: vec![],
                        //         catch: o.blocks[t].catch.clone(),
                        //         term: Default::default(),
                        //         orig_span: Some(f.span()),
                        //     });
                        //     let cfg: swc_cfg::Func = f.function.as_ref().clone().try_into()?;
                        //     let mut t4 = Trans {
                        //         map: Default::default(),
                        //         ret_to: Some((tmp.clone(), t2)),
                        //         recatch: o.blocks[t].catch.clone(),
                        //         this: Some((Atom::new("globalThis"), Default::default())),
                        //         import_mapper: static_map! {a => self.import_mapper[a].as_deref()},
                        //     };
                        //     let t3 = t4.trans(&cfg.cfg, o, cfg.entry)?;
                        //     o.blocks[t].term = TTerm::Jmp(t3);
                        //     return Ok((tmp, t2));
                        // }
                        _ => {
                            let r#fn;
                            (r#fn, t) = self.expr(i, o, b, t, e.as_ref())?;

                            match o.def(LId::Id { id: r#fn.clone() }).cloned() {
                                Some(Item::Func { func, arrow }) => {
                                    let u = Expr::undefined(call.span);
                                    for (p, a) in
                                        func.params.iter().map(Some).chain(once(None).cycle()).zip(
                                            call.args.iter().map(Some).chain(once(None).cycle()),
                                        )
                                    {
                                        if p.is_none() && a.is_none() {
                                            break;
                                        }
                                        // let Pat::Ident(id) = &p.pat else {
                                        //     anyhow::bail!("non-simple pattern")
                                        // };
                                        let arg;
                                        (arg, t) = self.expr(
                                            i,
                                            o,
                                            b,
                                            t,
                                            match a {
                                                Some(a) => &a.expr,
                                                None => &*u,
                                            },
                                        )?;
                                        if let Some(p) = p {
                                            o.blocks[t].stmts.push(TStmt {
                                                left: LId::Id { id: p.clone() },
                                                flags: Default::default(),
                                                right: Item::Just { id: arg },
                                                span: a.span(),
                                            });
                                        }
                                    }
                                    let tmp = o.regs.alloc(());
                                    let t2 = o.blocks.alloc(TBlock {
                                        stmts: vec![],
                                        post: TPostecedent {
                                            catch: o.blocks[t].post.catch.clone(),
                                            term: Default::default(),
                                            orig_span: Some(e.span()),
                                        },
                                    });
                                    let cfg: swc_cfg::Func = func.clone().try_into()?;
                                    let mut t4 = Trans {
                                        map: Default::default(),
                                        ret_to: Some((tmp.clone(), t2)),
                                        recatch: o.blocks[t].post.catch.clone(),
                                        this: if arrow || !func.cfg.has_this() {
                                            self.this.clone()
                                        } else {
                                            Some((Atom::new("globalThis"), Default::default()))
                                        },
                                        mapper: self.mapper.bud(),
                                    };
                                    let t3 = t4.trans(&cfg.cfg, o, cfg.entry)?;
                                    o.blocks[t].post.term = TTerm::Jmp(t3);
                                    return Ok((tmp, t2));
                                }
                                _ => TCallee::Val(r#fn),
                            }
                        }
                    },
                    _ => anyhow::bail!("todo: {}:{}", file!(), line!()),
                };
                let args: Vec<(Atom, SyntaxContext)> = call
                    .args
                    .iter()
                    .map(|a| {
                        let arg;
                        (arg, t) = self.expr(i, o, b, t, &a.expr)?;
                        anyhow::Ok(arg)
                    })
                    .collect::<anyhow::Result<_>>()?;
                match self
                    .mapper
                    .semantic
                    .flags
                    .contains(SemanticFlags::ASSUME_SES)
                    .then(|| {
                        let mut i;
                        match &c {
                            TCallee::Member { func, member } => {
                                match o.def(LId::Id { id: member.clone() })? {
                                    Item::Lit { lit: Lit::Str(s) } => match o
                                        .def(LId::Id { id: func.clone() })?
                                    {
                                        Item::Lit { lit } => ses_method(
                                            lit,
                                            &s.value,
                                            &mut match args.iter() {
                                                i2 => {
                                                    i = i2;
                                                    std::iter::from_fn(|| {
                                                        let n = i.next()?;
                                                        let i = o.def(LId::Id { id: n.clone() })?;
                                                        let Item::Lit { lit } = i else {
                                                            return None;
                                                        };
                                                        Some(lit.clone())
                                                    })
                                                    .fuse()
                                                }
                                            },
                                        ),
                                        _ => None,
                                    },
                                    _ => None,
                                }
                            }
                            _ => None,
                        }
                    })
                    .flatten()
                {
                    None => {
                        let tmp = o.regs.alloc(());
                        o.blocks[t].stmts.push(TStmt {
                            left: LId::Id { id: tmp.clone() },
                            flags: ValFlags::SSA_LIKE,
                            right: Item::Call { callee: c, args },
                            span: call.span(),
                        });
                        o.decls.insert(tmp.clone());
                        return Ok((tmp, t));
                    }
                    Some(l) => {
                        let tmp = o.regs.alloc(());
                        o.blocks[t].stmts.push(TStmt {
                            left: LId::Id { id: tmp.clone() },
                            flags: ValFlags::SSA_LIKE,
                            right: Item::Lit { lit: l },
                            span: call.span(),
                        });
                        o.decls.insert(tmp.clone());
                        return Ok((tmp, t));
                    }
                }
            }
            Expr::Bin(bin) => match (&*bin.left, &*bin.right, bin.op.clone()) {
                (Expr::PrivateName(p), obj, BinaryOp::In) => {
                    let o2;
                    (o2, t) = self.expr(i, o, b, t, obj)?;
                    let mem = Private {
                        sym: p.name.clone(),
                        ctxt: self
                            .mapper
                            .privates
                            .get(&p.name)
                            .cloned()
                            .context("in getting the private")?,
                        span: p.span,
                    };
                    let tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::HasPrivateMem { obj: o2, mem },
                        span: bin.span(),
                    });
                    o.decls.insert(tmp.clone());
                    return Ok((tmp, t));
                }
                (Expr::Lit(Lit::Str(s)), obj, BinaryOp::In)
                    if self
                        .mapper
                        .semantic
                        .flags
                        .contains(SemanticFlags::PLUGIN_AS_TILDE_PLUGIN)
                        && s.value == "~plugin" =>
                {
                    let o2;
                    (o2, t) = self.expr(i, o, b, t, obj)?;
                    let tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Lit {
                            lit: Lit::Bool(Bool {
                                span: s.span,
                                value: false,
                            }),
                        },
                        span: bin.span(),
                    });
                    o.decls.insert(tmp.clone());
                    return Ok((tmp, t));
                }
                (l, Expr::Lit(Lit::Num(Number { value: 0.0, .. })), BinaryOp::BitOr)
                | (Expr::Lit(Lit::Num(Number { value: 0.0, .. })), l, BinaryOp::BitOr) => {
                    let left;
                    // let right;
                    (left, t) = self.expr(i, o, b, t, l)?;
                    // (right, t) = self.expr(i, o, b, t, r)?;
                    let tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Asm {
                            value: Asm::OrZero(left),
                        },
                        span: bin.span(),
                    });
                    o.decls.insert(tmp.clone());
                    return Ok((tmp, t));
                }
                (l, r, op) => {
                    let left;
                    let right;
                    (left, t) = self.expr(i, o, b, t, l)?;
                    (right, t) = self.expr(i, o, b, t, r)?;
                    if left == right
                        && self
                            .mapper
                            .semantic
                            .flags
                            .contains(SemanticFlags::BITWISE_OR_ABSENT_NAN)
                    {
                        match op {
                            BinaryOp::EqEqEq => {
                                let tmp = o.regs.alloc(());
                                o.blocks[t].stmts.push(TStmt {
                                    left: LId::Id { id: tmp.clone() },
                                    flags: ValFlags::SSA_LIKE,
                                    right: Item::Lit {
                                        lit: Lit::Bool(Bool {
                                            span: bin.span,
                                            value: true,
                                        }),
                                    },
                                    span: bin.span(),
                                });
                                o.decls.insert(tmp.clone());
                                return Ok((tmp, t));
                            }
                            BinaryOp::NotEqEq => {
                                let tmp = o.regs.alloc(());
                                o.blocks[t].stmts.push(TStmt {
                                    left: LId::Id { id: tmp.clone() },
                                    flags: ValFlags::SSA_LIKE,
                                    right: Item::Lit {
                                        lit: Lit::Bool(Bool {
                                            span: bin.span,
                                            value: false,
                                        }),
                                    },
                                    span: bin.span(),
                                });
                                o.decls.insert(tmp.clone());
                                return Ok((tmp, t));
                            }
                            _ => {}
                        }
                    }
                    let tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Bin { left, right, op },
                        span: bin.span(),
                    });
                    o.decls.insert(tmp.clone());
                    return Ok((tmp, t));
                }
            },
            Expr::Unary(un) => {
                if un.op == UnaryOp::Void {
                    let tmp = o.regs.alloc(());
                    o.blocks[t].stmts.push(TStmt {
                        left: LId::Id { id: tmp.clone() },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Undef,
                        span: un.span(),
                    });
                    o.decls.insert(tmp.clone());
                    return Ok((tmp, t));
                }
                let arg;
                // let right;
                (arg, t) = self.expr(i, o, b, t, &un.arg)?;
                // (right, t) = self.expr(i, o, b, t, &bin.right)?;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Un {
                        arg,
                        op: un.op.clone(),
                    },
                    span: un.span(),
                });
                o.decls.insert(tmp.clone());
                return Ok((tmp, t));
            }
            Expr::Member(m) => return self.member_expr(i, o, b, t, m),
            Expr::Lit(l) => {
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Lit { lit: l.clone() },
                    span: l.span(),
                });
                o.decls.insert(tmp.clone());
                return Ok((tmp, t));
            }
            Expr::Fn(f) => {
                let tmp = match &f.ident {
                    Some(a) => a.clone().into(),
                    None => o.regs.alloc(()),
                };
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: Default::default(),
                    right: Item::Func {
                        func: f.function.as_ref().clone().try_into()?,
                        arrow: false,
                    },
                    span: f.span(),
                });
                o.decls.insert(tmp.clone());
                return Ok((tmp, t));
            }
            Expr::Arrow(a) => {
                let mut c = swc_cfg::Func::default();
                c.is_generator = a.is_generator;
                c.is_async = a.is_async;
                c.params = a
                    .params
                    .iter()
                    .cloned()
                    .map(|a| Param {
                        span: a.span(),
                        decorators: vec![],
                        pat: a,
                    })
                    .collect();
                let mut k = swc_cfg::ToCfgConversionCtx::default();
                match a.body.as_ref() {
                    swc_ecma_ast::BlockStmtOrExpr::BlockStmt(block_stmt) => {
                        k.transform_all(&mut c.cfg, block_stmt.stmts.clone(), c.entry)?;
                    }
                    swc_ecma_ast::BlockStmtOrExpr::Expr(expr) => {
                        c.cfg.blocks[c.entry].end = swc_cfg::End {
                            catch: swc_cfg::Catch::Throw,
                            orig_span: Some(a.span),
                            term: swc_cfg::Term::Return(Some(expr.as_ref().clone())),
                        }
                    }
                }
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: Default::default(),
                    right: Item::Func {
                        func: c.try_into()?,
                        arrow: true,
                    },
                    span: a.span(),
                });
                o.decls.insert(tmp.clone());
                return Ok((tmp, t));
            }
            Expr::Array(arr) => {
                let members = arr
                    .elems
                    .iter()
                    .flat_map(|a| a.as_ref())
                    .map(|x| {
                        anyhow::Ok({
                            let y;
                            (y, t) = self.expr(i, o, b, t, &x.expr)?;
                            y
                        })
                    })
                    .collect::<anyhow::Result<_>>()?;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Arr { members },
                    span: arr.span(),
                });
                o.decls.insert(tmp.clone());
                return Ok((tmp, t));
            }
            Expr::Object(obj) => {
                let members = obj
                    .props
                    .iter()
                    .map(|a| {
                        macro_rules! prop_name {
                            ($v:expr => $a:expr) => {
                                match $v {
                                    v => match $a {
                                        swc_ecma_ast::PropName::Ident(ident_name) => Some((
                                            PropKey::Lit((
                                                ident_name.sym.clone(),
                                                Default::default(),
                                            )),
                                            v,
                                        )),
                                        swc_ecma_ast::PropName::Str(s) => Some((
                                            PropKey::Lit((s.value.clone(), Default::default())),
                                            v,
                                        )),
                                        swc_ecma_ast::PropName::Num(number) => {
                                            anyhow::bail!("todo: {}:{}", file!(), line!())
                                        }
                                        swc_ecma_ast::PropName::Computed(computed_prop_name) => {
                                            let w;
                                            (w, t) =
                                                self.expr(i, o, b, t, &computed_prop_name.expr)?;
                                            Some((PropKey::Computed(w), v))
                                        }
                                        swc_ecma_ast::PropName::BigInt(big_int) => {
                                            anyhow::bail!("todo: {}:{}", file!(), line!())
                                        }
                                    },
                                }
                            };
                        }
                        anyhow::Ok(match a {
                            swc_ecma_ast::PropOrSpread::Spread(spread_element) => {
                                anyhow::bail!("todo: {}:{}", file!(), line!())
                            }
                            swc_ecma_ast::PropOrSpread::Prop(prop) => match prop.as_ref() {
                                swc_ecma_ast::Prop::Shorthand(ident) => Some((
                                    PropKey::Lit(ident.clone().into()),
                                    PropVal::Item(ident.clone().into()),
                                )),
                                swc_ecma_ast::Prop::KeyValue(key_value_prop) => {
                                    let v;
                                    (v, t) = self.expr(i, o, b, t, &key_value_prop.value)?;
                                    let v = PropVal::Item(v);
                                    prop_name!(v => &key_value_prop.key)
                                }
                                swc_ecma_ast::Prop::Assign(assign_prop) => {
                                    anyhow::bail!("todo: {}:{}", file!(), line!())
                                }
                                swc_ecma_ast::Prop::Getter(getter_prop) => {
                                    let v = PropVal::Getter({
                                        let mut c = swc_cfg::Func::default();
                                        let k = swc_cfg::ToCfgConversionCtx::default();
                                        let k = k.transform_all(
                                            &mut c.cfg,
                                            getter_prop
                                                .body
                                                .as_ref()
                                                .context("in getting the body")?
                                                .stmts
                                                .clone(),
                                            c.entry,
                                        )?;
                                        TFunc::try_from_with_mapper(&c, self.mapper.bud())?
                                    });
                                    prop_name!(v => &getter_prop.key)
                                }
                                swc_ecma_ast::Prop::Setter(setter_prop) => {
                                    let v = PropVal::Setter({
                                        let mut c = swc_cfg::Func::default();
                                        c.params.push(Param {
                                            span: setter_prop.span,
                                            decorators: vec![],
                                            pat: *setter_prop.param.clone(),
                                        });
                                        let k = swc_cfg::ToCfgConversionCtx::default();
                                        let k = k.transform_all(
                                            &mut c.cfg,
                                            setter_prop
                                                .body
                                                .as_ref()
                                                .context("in getting the body")?
                                                .stmts
                                                .clone(),
                                            c.entry,
                                        )?;
                                        TFunc::try_from_with_mapper(&c, self.mapper.bud())?
                                    });
                                    prop_name!(v => &setter_prop.key)
                                }
                                swc_ecma_ast::Prop::Method(method_prop) => {
                                    let v = PropVal::Method(TFunc::try_from_with_mapper(
                                        &(&*method_prop.function).clone().try_into()?,
                                        self.mapper.bud(),
                                    )?);
                                    prop_name!(v => &method_prop.key)
                                }
                            },
                        })
                    })
                    .filter_map(|a| match a {
                        Ok(Some(a)) => Some(Ok(a)),
                        Ok(None) => None,
                        Err(e) => Some(Err(e)),
                    })
                    .collect::<anyhow::Result<Vec<_>>>()?;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Obj { members },
                    span: obj.span(),
                });
                o.decls.insert(tmp.clone());
                return Ok((tmp, t));
            }
            Expr::Await(x) => {
                let (a, t) = self.expr(i, o, b, t, &x.arg)?;
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Await { value: a.clone() },
                    span: x.span(),
                });
                return Ok((tmp, t));
            }
            Expr::Yield(y) => {
                let y2 = match &y.arg {
                    None => None,
                    Some(a) => {
                        let b2;
                        (b2, t) = self.expr(i, o, b, t, a.as_ref())?;
                        Some(b2)
                    }
                };
                let tmp = o.regs.alloc(());
                o.blocks[t].stmts.push(TStmt {
                    left: LId::Id { id: tmp.clone() },
                    flags: ValFlags::SSA_LIKE,
                    right: Item::Yield {
                        value: y2,
                        delegate: y.delegate,
                    },
                    span: y.span(),
                });
                o.decls.insert(tmp.clone());
                return Ok((tmp, t));
            }
            Expr::Seq(s) => {
                let mut r = None;
                for a in s.exprs.iter() {
                    let c;
                    (c, t) = self.expr(i, o, b, t, a)?;
                    r = Some(c)
                }
                return Ok((r.context("in getting the last one")?, t));
            }
            _ => anyhow::bail!("todo: {}:{}", file!(), line!()),
        }
    }
}
