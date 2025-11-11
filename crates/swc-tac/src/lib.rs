//! Three-Address Code (TAC) intermediate representation for JavaScript.
//!
//! This crate provides a TAC representation for JavaScript/ECMAScript code, serving as an
//! intermediate layer between the Control Flow Graph (CFG) and Static Single Assignment (SSA)
//! forms in the compilation pipeline.
//!
//! # Three-Address Code
//!
//! TAC is a linear intermediate representation where each statement performs at most one
//! operation and uses at most three operands (typically: two sources and one destination).
//! This form makes data flow analysis and optimization easier than working directly with
//! the AST or CFG.
//!
//! # Key Types
//!
//! - [`TFunc`]: A complete function in TAC form, including its control flow graph
//! - [`TCfg`]: The control flow graph containing basic blocks and metadata
//! - [`TBlock`]: A single basic block containing a sequence of statements
//! - [`TStmt`]: A single statement assigning a value to a left-hand side identifier
//! - [`TTerm`]: A block terminator (return, jump, conditional branch, etc.)
//! - [`Item`]: The right-hand side of an assignment (operation, literal, call, etc.)
//! - [`LId`]: A left-hand side identifier (simple variable, member access, or private field)
//!
//! # Example Flow
//!
//! JavaScript code is transformed through these stages:
//! 1. Parse to AST (using SWC)
//! 2. Convert to CFG (using `swc-cfg`)
//! 3. Lower to TAC (this crate)
//! 4. Transform to SSA (using `swc-ssa`)
//!
//! # Modules
//!
//! - [`consts`]: Constant evaluation and propagation
//! - [`conv`]: Conversion from CFG to TAC
//! - [`lam`]: Lambda (function) handling and atom resolution
//! - [`prepa`]: Preparation and preprocessing passes
//! - [`rew`]: Rewriting and transformation passes
//! - [`splat`]: Object and array spreading operations

use anyhow::Context;
use arena_traits::IndexAlloc;
use bitflags::bitflags;
use either::Either;
use id_arena::{Arena, Id};
use lam::LAM;
use linearize::{StaticMap, static_map};
use portal_jsc_common::semantic;
use portal_jsc_common::{natives::Native, syntax::Asm};
use portal_jsc_swc_util::brighten::Purity;
use portal_jsc_swc_util::{ImportMapper, ResolveNatives, SemanticCfg, SemanticFlags, ses_method};
use portal_solutions_swibb::ConstCollector;
use ssa_impls::dom::{dominates, domtree};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::convert::Infallible;
use std::iter::{empty, once};
use std::mem::take;
use std::sync::Arc;
use swc_atoms::{Atom, Wtf8Atom};
use swc_cfg::{Block, Catch, Cfg, Func};
use swc_common::{EqIgnoreSpan, Mark, Span, Spanned, SyntaxContext};
use swc_ecma_ast::Id as Ident;
use swc_ecma_ast::{
    AssignExpr, AssignOp, AssignTarget, BinaryOp, Bool, Callee, Class, ClassMember,
    ComputedPropName, CondExpr, Expr, Function, Lit, MemberExpr, MemberProp, MetaPropKind, Number,
    Param, Pat, SimpleAssignTarget, Stmt, Str, TsType, TsTypeAnn, TsTypeParamDecl, UnaryOp,
};
// use crate::consts::{ItemGetter, ItemGetterExt};
use crate::lam::{AtomResolver, DefaultAtomResolver};
pub use swc_ll_common::*;
pub mod consts;
pub mod conv;
pub mod lam;
pub mod prepa;
pub mod rew;
pub mod splat;
/// A left-hand side identifier in an assignment statement.
///
/// In TAC, the left-hand side of an assignment can be:
/// - A simple variable identifier
/// - A member access (e.g., `obj.property` or `obj[computed]`)
/// - A private field access (using JavaScript private field syntax)
///
/// # Type Parameters
///
/// - `I`: The identifier type (defaults to SWC's `Ident`)
/// - `M`: The member name type (defaults to a single-element array `[I; 1]`)
///
/// # Examples
///
/// ```ignore
/// // Simple assignment: x = ...
/// LId::Id { id: x }
///
/// // Member assignment: obj.prop = ...
/// LId::Member { obj, mem: [prop] }
///
/// // Private field: obj.#private = ...
/// LId::Private { obj, id: private_symbol }
/// ```
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum LId<I = Ident, M = [I; 1]> {
    /// A simple variable identifier
    Id { id: I },
    /// A member access (property or computed member)
    Member { obj: I, mem: M },
    /// A private field access
    Private { obj: I, id: Private },
    // SplitOff { head: I, tail: I },
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
            // LId::SplitOff { head, tail } => LId::SplitOff { head, tail },
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
            // LId::SplitOff { head, tail } => LId::SplitOff { head, tail },
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
            // LId::SplitOff { head, tail } => Either::Right(Either::Right([head, tail].into_iter())),
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
            // LId::SplitOff { head, tail } => LId::SplitOff {
            //     head: f(cx, head)?,
            //     tail: f(cx, tail)?,
            // },
        })
    }
}
#[cfg(feature = "simpl-legacy")]
pub mod simpl_legacy;
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
                value: ident_name.sym.into(),
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
    /// Flags associated with values in TAC statements.
    ///
    /// These flags track properties of values that are useful for optimization
    /// and analysis.
    #[repr(transparent)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
    pub struct ValFlags: u64{
        /// Indicates this value is in SSA-like form.
        ///
        /// When set, this value is assigned exactly once and dominates all its uses,
        /// similar to SSA form. This allows certain optimizations that rely on
        /// single-assignment semantics.
        const SSA_LIKE = 0x1;
    }
}
/// A function in Three-Address Code (TAC) form.
///
/// This represents a complete function with its control flow graph, parameters,
/// and metadata. The function consists of basic blocks connected by control flow,
/// with one designated entry block.
///
/// # Fields
///
/// - `cfg`: The control flow graph containing all basic blocks
/// - `entry`: The entry block where execution begins
/// - `params`: Function parameter identifiers
/// - `ts_params`: Optional TypeScript type annotations for parameters
/// - `is_generator`: Whether this is a generator function
/// - `is_async`: Whether this is an async function
#[derive(Clone, Debug)]
pub struct TFunc {
    /// The control flow graph containing all basic blocks
    pub cfg: TCfg,
    /// The entry block identifier (where execution starts)
    pub entry: Id<TBlock>,
    /// Function parameter identifiers
    pub params: Vec<Ident>,
    /// Optional TypeScript type annotations for parameters
    pub ts_params: Vec<Option<TsType>>,
    /// Whether this is a generator function (function*)
    pub is_generator: bool,
    /// Whether this is an async function
    pub is_async: bool,
}
#[derive(Clone)]
#[non_exhaustive]
pub struct Mapper<'a> {
    pub import_mapper: StaticMap<ImportMapperReq, Option<&'a (dyn ImportMapper + 'a)>>,
    pub semantic: &'a SemanticCfg,
    pub privates: &'a BTreeMap<Atom, SyntaxContext>,
    pub consts: Option<&'a ConstCollector>,
    pub vars: Arc<dyn AtomResolver>,
    pub to_cfg: &'a (dyn Fn(&Function) -> anyhow::Result<Func> + 'a),
}
pub fn mapped<T>(a: impl FnOnce(Mapper<'_>) -> T) -> T {
    return a(Mapper {
        import_mapper: static_map! {_ => None},
        semantic: &SemanticCfg::default(),
        privates: &BTreeMap::new(),
        consts: None,
        vars: Arc::new(DefaultAtomResolver {}),
        to_cfg: &|a| a.clone().try_into(),
    });
}
impl<'a> Mapper<'a> {
    pub fn bud(&self) -> Mapper<'_> {
        Mapper {
            import_mapper: static_map! {a =>self.import_mapper[a].as_deref()},
            semantic: self.semantic,
            privates: self.privates,
            consts: self.consts.as_deref(),
            vars: self.vars.clone(),
            to_cfg: self.to_cfg,
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
impl Default for TFunc {
    fn default() -> Self {
        let mut cfg = TCfg::default();
        let entry = cfg.blocks.alloc(Default::default());
        Self {
            cfg,
            entry,
            params: Default::default(),
            ts_params: Default::default(),
            is_generator: Default::default(),
            is_async: Default::default(),
        }
    }
}
/// The Control Flow Graph (CFG) for a function in TAC form.
///
/// Contains all the basic blocks that make up a function, along with metadata
/// about variables, types, and register allocation.
///
/// # Fields
///
/// - `blocks`: Arena of all basic blocks in the function
/// - `regs`: Register allocator/manager (LAM - Local Allocation Map)
/// - `decls`: Set of all declared variables in the function
/// - `type_annotations`: TypeScript type annotations for variables
/// - `generics`: Optional generic type parameters for the function
/// - `ts_retty`: Optional TypeScript return type annotation
#[derive(Default, Clone, Debug)]
pub struct TCfg {
    /// Arena containing all basic blocks
    pub blocks: Arena<TBlock>,
    /// Register allocator/manager for temporary values
    pub regs: LAM<()>,
    /// Set of all declared variables in this function
    pub decls: BTreeSet<Ident>,
    /// TypeScript type annotations for variables
    pub type_annotations: BTreeMap<Ident, TsType>,
    /// Generic type parameters (if this is a generic function)
    pub generics: Option<TsTypeParamDecl>,
    /// TypeScript return type annotation
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
    pub fn def(&self, i: LId<Ident>) -> Option<&Item<Ident, TFunc>> {
        self.blocks.iter().flat_map(|a| &a.1.stmts).find_map(|a| {
            if a.left == i && a.flags.contains(ValFlags::SSA_LIKE) {
                Some(&a.right)
            } else {
                None
            }
        })
    }
    pub fn def_mut(&mut self, i: LId<Ident>) -> Option<&mut Item<Ident, TFunc>> {
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
    pub fn taints_object(&self, a: &Ident) -> bool {
        return self.blocks.iter().any(|s| {
            s.1.stmts.iter().any(|s| {
                s.left.taints_object(a)
                    || s.right
                        .funcs()
                        .any(|f| f.cfg.taints_object(a) || s.right.taints_object(a))
            }) || s.1.post.term.taints_object(a)
        });
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
                TTerm::Tail { callee, args } => Box::new(
                    match callee {
                        TCallee::Val(a) | TCallee::PrivateMember { func: a, member: _ } => {
                            vec![a]
                        }
                        TCallee::Member { func: r#fn, member } => vec![r#fn, member],
                        TCallee::Import | TCallee::Super | TCallee::Eval => vec![], // swc_tac::TCallee::Static(_) => vec![],
                    }
                    .into_iter()
                    .cloned()
                    .chain(
                        args.iter()
                            .map(
                                |SpreadOr {
                                     value: a,
                                     is_spread: _,
                                 }| a,
                            )
                            .cloned(),
                    ),
                ),
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
    pub fn glue_nothrows(&mut self) {
        'a: loop {
            for k in self.blocks.iter().map(|a| a.0).collect::<BTreeSet<_>>() {
                if let TTerm::Jmp(a) = &self.blocks[k].post.term {
                    let a = *a;
                    if a != k {
                        if self.blocks[a].stmts.iter().all(|s| s.nothrow())
                            || &self.blocks[k].post.catch == &self.blocks[a].post.catch
                        {
                            let s = self.blocks[a].stmts.clone();
                            self.blocks[k].stmts.extend(s);
                            self.blocks[k].post.term = self.blocks[a].post.term.clone();
                            continue 'a;
                        }
                    }
                }
            }
            return;
        }
    }
    pub fn stripe(&mut self) {
        let mut decls = self.decls.clone();
        let mut d = BTreeMap::new();
        for e in self.externs().collect::<BTreeSet<_>>() {
            decls.remove(&e);
            d.insert(e, 0usize);
        }
        for (k, l) in self.blocks.iter_mut() {
            let mut pi = 0usize;
            for _ in l.stmts.splice(
                0..0,
                d.iter_mut().map(|(a, b)| {
                    *b += 1;
                    pi += 1;
                    TStmt {
                        left: LId::Id {
                            id: (Atom::new(format!("_{}${b}", &a.0)), a.1),
                        },
                        flags: ValFlags::SSA_LIKE,
                        right: Item::Just { id: a.clone() },
                        span: l.post.orig_span.unwrap_or_default(),
                    }
                }),
            ) {}
            for s in l.stmts.iter_mut().skip(pi) {
                s.right = s
                    .right
                    .as_ref()
                    .map2(
                        &mut (),
                        &mut |_, a| {
                            Ok(match d.get(a) {
                                None => a.clone(),
                                Some(b) => (Atom::new(format!("_{}${b}", &a.0)), a.1),
                            })
                        },
                        &mut |a, b| {
                            Ok::<_, Infallible>({
                                let mut b = b.clone();
                                b.cfg.stripe();
                                b
                            })
                        },
                    )
                    .unwrap();
                if let LId::Id { id } = &mut s.left {
                    if let Some(b) = d.get_mut(id) {
                        *b += 1;
                        id.0 = Atom::new(format!("_{}${b}", &id.0));
                    }
                }
            }
            for (a, b) in d.iter() {
                let t = Atom::new(format!("_{}${b}", &a.0));
                l.stmts.push(TStmt {
                    left: LId::Id { id: a.clone() },
                    flags: ValFlags::empty(),
                    right: Item::Just { id: (t, a.1) },
                    span: l.post.orig_span.unwrap_or_default(),
                });
            }
        }
    }
    pub fn splat_objects(
        &mut self,
        d: BTreeMap<Option<Id<TBlock>>, Id<TBlock>>,
        semantic: SemanticCfg,
    ) {
        let mut cont = true;
        #[derive(Clone)]
        enum PropKind {
            Item(Ident, Ident),
            Prop {
                getter: Option<TFunc>,
                setter: Option<TFunc>,
            },
        }
        impl PropKind {
            pub fn to_render(
                self,
                key: PropKey<Ident>,
                regs: &LAM<()>,
            ) -> Vec<(PropKey<Ident>, PropVal<Ident, TFunc>)> {
                match self {
                    PropKind::Item(_, w) => [
                        (
                            key.clone(),
                            PropVal::Getter({
                                let mut f = TFunc::default();
                                f.cfg.regs.resolver = regs.resolver.clone();
                                f.cfg.blocks[f.entry].post.term = TTerm::Return(Some(w.clone()));
                                f
                            }),
                        ),
                        (
                            key.clone(),
                            PropVal::Setter({
                                let mut f = TFunc::default();
                                f.cfg.regs.resolver = regs.resolver.clone();
                                let p = f.cfg.regs.alloc(());
                                f.params.push(p.clone());
                                f.cfg.blocks[f.entry].stmts.push(TStmt {
                                    left: LId::Id { id: w.clone() },
                                    flags: Default::default(),
                                    right: Item::Just { id: p },
                                    span: Span::dummy_with_cmt(),
                                });
                                f.cfg.blocks[f.entry].post.term = TTerm::Return(Some(w.clone()));
                                f
                            }),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                    PropKind::Prop { getter, setter } => getter
                        .map(|a| (key.clone(), PropVal::Getter(a)))
                        .into_iter()
                        .chain(setter.map(|a| (key.clone(), PropVal::Setter(a))))
                        .collect(),
                }
            }
        }
        while take(&mut cont) {
            self.remark_with_domtree(d.clone());
            self.simplify_justs();
            self.remark_with_domtree(d.clone());
            let mut a = self
                .decls
                .clone()
                .into_iter()
                // .filter_map(|a|)
                .filter_map(|a| match self.get_item(a.clone())? {
                    Item::Obj { members } => {
                        // let mut a = Vec::default();
                        let mut m = HashMap::new();
                        for (k, v) in members.clone().into_iter() {
                            let mut k = match k {
                                PropKey::Lit(l) => Lit::Str(Str {
                                    span: Span::dummy_with_cmt(),
                                    value: l.0.clone().into(),
                                    raw: None,
                                }),
                                PropKey::Computed(c) => match self.get_item(c)? {
                                    Item::Lit { lit } => lit.clone(),
                                    _ => return None,
                                },
                                _ => return None,
                            };
                            match v {
                                PropVal::Item(v) => {
                                    k.set_span(Span::dummy_with_cmt());
                                    m.insert(k, PropKind::Item(v, self.regs.alloc(())));
                                }
                                PropVal::Getter(g)
                                    if semantic
                                        .flags
                                        .contains(SemanticFlags::NO_MONKEYPATCHING)
                                        || !g.cfg.has_this() =>
                                {
                                    let PropKind::Prop { getter, setter } =
                                        m.entry(k).or_insert_with(|| PropKind::Prop {
                                            getter: None,
                                            setter: None,
                                        })
                                    else {
                                        return None;
                                    };
                                    *getter = Some(g)
                                }
                                PropVal::Setter(s)
                                    if semantic
                                        .flags
                                        .contains(SemanticFlags::NO_MONKEYPATCHING)
                                        || !s.cfg.has_this() =>
                                {
                                    let PropKind::Prop { getter, setter } =
                                        m.entry(k).or_insert_with(|| PropKind::Prop {
                                            getter: None,
                                            setter: None,
                                        })
                                    else {
                                        return None;
                                    };
                                    *setter = Some(s);
                                }
                                _ => return None,
                            }
                            // a.push((k.clone(), v.clone()));
                        }
                        Some((a.clone(), m))
                    }
                    Item::Arr { members } => {
                        let mut m = HashMap::new();
                        for (i, v) in members.clone().into_iter().enumerate() {
                            if v.is_spread {
                                return None;
                            };
                            let v = v.value;
                            let mut k = Lit::Num(Number {
                                span: Span::dummy_with_cmt(),
                                value: i as f64,
                                raw: None,
                            });
                            k.set_span(Span::dummy_with_cmt());
                            m.insert(k, PropKind::Item(v, self.regs.alloc(())));
                            // a.push((k.clone(), v.clone()));
                        }
                        Some((a.clone(), m))
                    }
                    _ => None,
                })
                .collect::<BTreeMap<_, _>>();
            a = a
                .into_iter()
                .filter(|(a, _)| {
                    !self.blocks.iter().any(|k| {
                        k.1.stmts.iter().any(|s| s.will_ruin(a))
                            || match &k.1.post.term {
                                TTerm::Return(Some(b)) => b == a,
                                TTerm::Throw(b) => b == a,
                                _ => false,
                            }
                    })
                })
                .collect();
            for ki in self.blocks.iter().map(|a| a.0).collect::<BTreeSet<_>>() {
                // let mut k = &mut;
                's: for mut s in take(&mut self.blocks[ki].stmts) {
                    if let LId::Id { id } = &s.left {
                        if let Some(v) = a.get(id) {
                            for p in v.values() {
                                match p {
                                    PropKind::Item(v, t) => {
                                        self.blocks[ki].stmts.push(TStmt {
                                            left: LId::Id { id: t.clone() },
                                            flags: Default::default(),
                                            right: Item::Just { id: v.clone() },
                                            span: s.span,
                                        });
                                    }
                                    PropKind::Prop { getter, setter } => {}
                                }
                                cont = true;
                            }
                            continue;
                        }
                    }
                    'a: {
                        if let LId::Member { obj, mem } = &s.left {
                            if let Some(v) = a.get(obj) {
                                if let Some(Item::Lit { lit }) = self.get_item(mem[0].clone()) {
                                    let mut lit = lit.clone();
                                    lit.set_span(Span::dummy_with_cmt());
                                    if let Some(w) = v.get(&lit) {
                                        match w {
                                            PropKind::Item(_, w) => {
                                                s.left = LId::Id { id: w.clone() };
                                            }
                                            PropKind::Prop { getter, setter } => {
                                                let stub = self.regs.alloc(());
                                                if let Some(setter) = setter {
                                                    let tmp = self.regs.alloc(());
                                                    let tmp2 = self.regs.alloc(());
                                                    let tmp3 = self.regs.alloc(());

                                                    self.blocks[ki].stmts.push(TStmt {
                                                        left: LId::Id { id: tmp2.clone() },
                                                        flags: ValFlags::SSA_LIKE,
                                                        right: Item::Obj {
                                                            members: v
                                                                .iter()
                                                                .flat_map(|(a, b)| {
                                                                    b.clone().to_render(
                                                                        PropKey::Lit(match a {
                                                                            Lit::Str(s) => (
                                                                                (&*s.value.clone().to_atom_lossy()).clone(),
                                                                                Default::default(),
                                                                            ),
                                                                            _ => todo!(),
                                                                        }),
                                                                        &self.regs,
                                                                    )
                                                                })
                                                                .collect(),
                                                        },
                                                        span: s.span,
                                                    });
                                                    self.blocks[ki].stmts.push(TStmt {
                                                        left: LId::Id { id: tmp.clone() },
                                                        flags: ValFlags::SSA_LIKE,
                                                        right: Item::Func {
                                                            func: setter.clone(),
                                                            arrow: false,
                                                        },
                                                        span: s.span,
                                                    });
                                                    self.blocks[ki].stmts.push(TStmt {
                                                        left: LId::Id { id: tmp3.clone() },
                                                        flags: ValFlags::SSA_LIKE,
                                                        right: Item::Lit {
                                                            lit: Lit::Str(Str {
                                                                span: s.span,
                                                                value: Wtf8Atom::new("call"),
                                                                raw: None,
                                                            }),
                                                        },
                                                        span: s.span,
                                                    });
                                                    s.left = LId::Id { id: stub.clone() };
                                                    let span = s.span;
                                                    self.blocks[ki].stmts.push(s);
                                                    s = TStmt {
                                                        left: LId::Id { id: stub.clone() },
                                                        flags: ValFlags::default(),
                                                        right: Item::Call {
                                                            callee: if semantic.flags.contains(
                                                                SemanticFlags::NO_MONKEYPATCHING,
                                                            ) {
                                                                TCallee::Member {
                                                                    func: tmp,
                                                                    member: tmp3,
                                                                }
                                                            } else {
                                                                TCallee::Val(tmp)
                                                            },
                                                            args: [tmp2, stub]
                                                                .into_iter()
                                                                .map(|a| SpreadOr {
                                                                    value: a,
                                                                    is_spread: false,
                                                                }) .skip(
                                                            if semantic.flags.contains(
                                                                SemanticFlags::NO_MONKEYPATCHING,
                                                            ) {
                                                                0
                                                            } else {
                                                                1
                                                            },
                                                        )
                                                                .collect(),
                                                        },
                                                        span: span,
                                                    }
                                                } else {
                                                    s.left = LId::Id { id: stub };
                                                }
                                            }
                                        };
                                        cont = true;
                                        break 'a;
                                    }
                                }
                            }
                        }
                    }
                    'b: {
                        if let Item::Mem { obj, mem } = &s.right {
                            if let Some(v) = a.get(obj) {
                                if let Some(Item::Lit { lit }) = self.get_item(mem.clone()) {
                                    let mut lit = lit.clone();
                                    lit.set_span(Span::dummy_with_cmt());
                                    if let Some(w) = v.get(&lit) {
                                        match w {
                                            PropKind::Item(_, w) => {
                                                s.right = Item::Just { id: w.clone() };
                                            }
                                            PropKind::Prop { getter, setter } => {
                                                if let Some(getter) = getter {
                                                    let tmp = self.regs.alloc(());
                                                    let tmp2 = self.regs.alloc(());
                                                    let tmp3 = self.regs.alloc(());

                                                    self.blocks[ki].stmts.push(TStmt {
                                                        left: LId::Id { id: tmp2.clone() },
                                                        flags: ValFlags::SSA_LIKE,
                                                        right: Item::Obj {
                                                            members: v
                                                                .iter()
                                                                .flat_map(|(a, b)| {
                                                                    b.clone().to_render(
                                                                        PropKey::Lit(match a {
                                                                            Lit::Str(s) => (
                                                                                (&*s.value.to_atom_lossy()).clone(),
                                                                                Default::default(),
                                                                            ),
                                                                            _ => todo!(),
                                                                        }),
                                                                        &self.regs,
                                                                    )
                                                                })
                                                                .collect(),
                                                        },
                                                        span: s.span,
                                                    });
                                                    self.blocks[ki].stmts.push(TStmt {
                                                        left: LId::Id { id: tmp.clone() },
                                                        flags: ValFlags::SSA_LIKE,
                                                        right: Item::Func {
                                                            func: getter.clone(),
                                                            arrow: false,
                                                        },
                                                        span: s.span,
                                                    });
                                                    self.blocks[ki].stmts.push(TStmt {
                                                        left: LId::Id { id: tmp3.clone() },
                                                        flags: ValFlags::SSA_LIKE,
                                                        right: Item::Lit {
                                                            lit: Lit::Str(Str {
                                                                span: s.span,
                                                                value: Wtf8Atom::new("call"),
                                                                raw: None,
                                                            }),
                                                        },
                                                        span: s.span,
                                                    });
                                                    s.right = Item::Call {
                                                        callee: if semantic.flags.contains(
                                                            SemanticFlags::NO_MONKEYPATCHING,
                                                        ) {
                                                            TCallee::Member {
                                                                func: tmp,
                                                                member: tmp3,
                                                            }
                                                        } else {
                                                            TCallee::Val(tmp)
                                                        },
                                                        args: [SpreadOr {
                                                            is_spread: false,
                                                            value: tmp2,
                                                        }]
                                                        .into_iter()
                                                        .skip(
                                                            if semantic.flags.contains(
                                                                SemanticFlags::NO_MONKEYPATCHING,
                                                            ) {
                                                                0
                                                            } else {
                                                                1
                                                            },
                                                        )
                                                        .collect(),
                                                    }
                                                } else {
                                                    s.right = Item::Undef;
                                                }
                                            }
                                        };
                                        cont = true;
                                        break 'b;
                                    }
                                }
                            }
                        }
                    }
                    self.blocks[ki].stmts.push(s);
                }
            }
        }
    }
}
impl Externs<Ident> for TCfg {
    fn externs(&self) -> impl Iterator<Item = Ident> {
        TCfg::externs(self)
    }
}
/// A statement in Three-Address Code (TAC) form.
///
/// Each statement represents a single operation that assigns a value to a
/// left-hand side identifier. This is the basic unit of computation in TAC.
///
/// # Structure
///
/// ```text
/// left = right
/// ```
///
/// Where:
/// - `left` is an [`LId`] (identifier, member access, or private field)
/// - `right` is an [`Item`] (operation, literal, call, etc.)
///
/// # Fields
///
/// - `left`: The target of the assignment
/// - `flags`: Properties of this value (e.g., SSA_LIKE)
/// - `right`: The value being computed and assigned
/// - `span`: Source location information for error reporting
#[derive(Clone, Debug)]
pub struct TStmt {
    /// The left-hand side (target) of the assignment
    pub left: LId,
    /// Flags indicating properties of this value
    pub flags: ValFlags,
    /// The right-hand side (value) being assigned
    pub right: Item<Ident, TFunc>,
    /// Source span for debugging and error reporting
    pub span: Span,
}
impl TStmt {
    pub fn will_ruin(&self, i: &Ident) -> bool {
        self.right.will_ruin(i)
    }
    pub fn will_store(&self, i: &Ident) -> bool {
        match &self.left {
            LId::Id { id } if id == i => true,
            _ => self.right.will_store(i),
        }
    }
}
impl<I, M> LId<I, M> {
    pub fn nothrow(&self) -> bool {
        match self {
            LId::Id { id } => true,
            _ => false,
        }
    }
}
impl TStmt {
    pub fn nothrow(&self) -> bool {
        return self.left.nothrow() && self.right.nothrow();
    }
}
/// A basic block in the control flow graph.
///
/// A basic block is a sequence of statements with a single entry point (the first
/// statement) and a single exit point (the terminator). Control flow can only
/// enter at the beginning and leave at the end.
///
/// # Structure
///
/// ```text
/// Block:
///   stmt1
///   stmt2
///   ...
///   stmtN
///   terminator (return, jump, conditional, etc.)
/// ```
///
/// # Fields
///
/// - `stmts`: Sequence of statements executed in order
/// - `post`: The postcedent (terminator and exception handler) that ends the block
#[derive(Clone, Default, Debug)]
pub struct TBlock {
    /// Statements in this basic block, executed sequentially
    pub stmts: Vec<TStmt>,
    /// The postcedent (terminator and exception handling)
    pub post: TPostecedent,
}
/// The postcedent (exit point) of a basic block.
///
/// Each basic block ends with a postcedent that specifies:
/// 1. How control flow continues (the terminator)
/// 2. How exceptions are handled (the catch handler)
///
/// # Type Parameters
///
/// - `B`: Block identifier type (defaults to `Id<TBlock>`)
/// - `I`: Identifier type (defaults to `Ident`)
///
/// # Fields
///
/// - `catch`: Exception handler for this block
/// - `term`: The terminator specifying normal control flow
/// - `orig_span`: Original source span for debugging
#[derive(Clone, Debug)]
pub struct TPostecedent<B = Id<TBlock>, I = Ident> {
    /// Exception handler specification
    pub catch: TCatch<B, I>,
    /// Normal control flow terminator
    pub term: TTerm<B, I>,
    /// Original source location
    pub orig_span: Option<Span>,
}
impl<B, I> Default for TPostecedent<B, I> {
    fn default() -> Self {
        Self {
            catch: Default::default(),
            term: Default::default(),
            orig_span: Default::default(),
        }
    }
}
pub mod impls;
/// Exception handling specification for a basic block.
///
/// Specifies what happens when an exception is thrown during execution of
/// the basic block's statements.
///
/// # Type Parameters
///
/// - `B`: Block identifier type (defaults to `Id<TBlock>`)
/// - `I`: Identifier type (defaults to `Ident`)
///
/// # Variants
///
/// - `Throw`: Propagate the exception to the caller (no catch handler)
/// - `Jump`: Jump to a catch handler block, binding the exception to a pattern
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TCatch<B = Id<TBlock>, I = Ident> {
    // #[default]
    /// No exception handler - throw to caller
    Throw,
    /// Jump to a catch block, binding exception to `pat`
    Jump {
        /// Pattern (identifier) to bind the exception value to
        pat: I,
        /// The catch handler block to jump to
        k: B,
    },
}
impl<B, I> Default for TCatch<B, I> {
    fn default() -> Self {
        Self::Throw
    }
}
impl<B, I> TCatch<B, I> {
    pub fn as_ref<'a>(&'a self) -> TCatch<&'a B, &'a I> {
        match self {
            Self::Throw => TCatch::Throw,
            Self::Jump { pat, k } => TCatch::Jump { pat, k },
        }
    }
    pub fn as_mut<'a>(&'a mut self) -> TCatch<&'a mut B, &'a mut I> {
        match self {
            Self::Throw => TCatch::Throw,
            Self::Jump { pat, k } => TCatch::Jump { pat, k },
        }
    }
    pub fn map<Cx, E, B2, I2>(
        self,
        cx: &mut Cx,
        b: &mut (dyn FnMut(&mut Cx, B) -> Result<B2, E> + '_),
        i: &mut (dyn FnMut(&mut Cx, I) -> Result<I2, E> + '_),
    ) -> Result<TCatch<B2, I2>, E> {
        Ok(match self {
            TCatch::Throw => TCatch::Throw,
            TCatch::Jump { pat, k } => TCatch::Jump {
                pat: i(cx, pat)?,
                k: b(cx, k)?,
            },
        })
    }
}
/// A block terminator specifying control flow.
///
/// Every basic block ends with exactly one terminator that determines where
/// control flow goes next. Terminators represent all the ways control can
/// leave a block: returns, throws, jumps, and branches.
///
/// # Type Parameters
///
/// - `B`: Block identifier type (defaults to `Id<TBlock>`)
/// - `I`: Identifier type (defaults to `Ident`)
///
/// # Variants
///
/// - `Return`: Return from the function (optionally with a value)
/// - `Tail`: Tail call optimization - call and return in one step
/// - `Throw`: Throw an exception
/// - `Jmp`: Unconditional jump to another block
/// - `CondJmp`: Conditional branch (if-then-else)
/// - `Switch`: Multi-way branch based on a value
/// - `Default`: Placeholder/unreachable terminator
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TTerm<B = Id<TBlock>, I = Ident> {
    /// Return from function, optionally with a value
    Return(Option<I>),
    /// Tail call - call function and immediately return its result
    Tail {
        /// The function being called
        callee: TCallee<I>,
        /// Arguments to the function call
        args: Vec<SpreadOr<I>>,
    },
    /// Throw an exception with the given value
    Throw(I),
    /// Unconditional jump to a block
    Jmp(B),
    /// Conditional jump based on a boolean condition
    CondJmp {
        /// The condition value (should be boolean)
        cond: I,
        /// Block to jump to if condition is true
        if_true: B,
        /// Block to jump to if condition is false
        if_false: B,
    },
    /// Multi-way branch (switch statement)
    Switch {
        /// The value being switched on
        x: I,
        /// List of (case_value, target_block) pairs
        blocks: Vec<(I, B)>,
        /// Default block if no case matches
        default: B,
    },
    // #[default]
    /// Placeholder or unreachable terminator
    Default,
}
impl<I: Eq, M> LId<I, M> {
    pub fn taints_object(&self, a: &I) -> bool {
        match self {
            LId::Member { obj, mem } if obj == a => true,
            _ => false,
        }
    }
}
impl<B, I: Eq> TTerm<B, I> {
    pub fn taints_object(&self, a: &I) -> bool {
        match self {
            _ => false,
        }
    }
}
impl<B, I> TTerm<B, I> {
    pub fn as_ref<'a>(&'a self) -> TTerm<&'a B, &'a I>
where
        // I: Eq + std::hash::Hash,
    {
        match self {
            TTerm::Return(a) => TTerm::Return(a.as_ref()),
            TTerm::Throw(t) => TTerm::Throw(t),
            TTerm::Jmp(j) => TTerm::Jmp(j),
            TTerm::CondJmp {
                cond,
                if_true,
                if_false,
            } => TTerm::CondJmp {
                cond,
                if_true,
                if_false,
            },
            TTerm::Switch { x, blocks, default } => TTerm::Switch {
                x,
                blocks: blocks.iter().map(|(a, b)| (a, b)).collect(),
                default,
            },
            TTerm::Default => TTerm::Default,
            TTerm::Tail { callee, args } => TTerm::Tail {
                callee: callee.as_ref(),
                args: args
                    .iter()
                    .map(
                        |SpreadOr {
                             value: a,
                             is_spread: b,
                         }| SpreadOr {
                            value: a,
                            is_spread: *b,
                        },
                    )
                    .collect(),
            },
        }
    }
    pub fn as_mut<'a>(&'a mut self) -> TTerm<&'a mut B, &'a mut I>
where
        // I: Eq + std::hash::Hash,
    {
        match self {
            TTerm::Return(a) => TTerm::Return(a.as_mut()),
            TTerm::Throw(t) => TTerm::Throw(t),
            TTerm::Jmp(j) => TTerm::Jmp(j),
            TTerm::CondJmp {
                cond,
                if_true,
                if_false,
            } => TTerm::CondJmp {
                cond,
                if_true,
                if_false,
            },
            TTerm::Switch { x, blocks, default } => TTerm::Switch {
                x,
                blocks: blocks.iter_mut().map(|(a, b)| (a, b)).collect(),
                default,
            },
            TTerm::Default => TTerm::Default,
            TTerm::Tail { callee, args } => TTerm::Tail {
                callee: callee.as_mut(),
                args: args
                    .iter_mut()
                    .map(
                        |SpreadOr {
                             value: a,
                             is_spread: b,
                         }| SpreadOr {
                            value: a,
                            is_spread: *b,
                        },
                    )
                    .collect(),
            },
        }
    }
    pub fn map<Cx, E, B2, I2>(
        self,
        cx: &mut Cx,
        block: &mut (dyn FnMut(&mut Cx, B) -> Result<B2, E> + '_),
        ident: &mut (dyn FnMut(&mut Cx, I) -> Result<I2, E> + '_),
    ) -> Result<TTerm<B2, I2>, E>
where
        // I2: Eq + std::hash::Hash,
    {
        Ok(match self {
            TTerm::Return(a) => TTerm::Return(match a {
                None => None,
                Some(a) => Some(ident(cx, a)?),
            }),
            TTerm::Throw(v) => TTerm::Throw(ident(cx, v)?),
            TTerm::Jmp(v) => TTerm::Jmp(block(cx, v)?),
            TTerm::CondJmp {
                cond,
                if_true,
                if_false,
            } => TTerm::CondJmp {
                cond: ident(cx, cond)?,
                if_true: block(cx, if_true)?,
                if_false: block(cx, if_false)?,
            },
            TTerm::Switch { x, blocks, default } => TTerm::Switch {
                x: ident(cx, x)?,
                blocks: blocks
                    .into_iter()
                    .map(|(a, c)| Ok::<_, E>((ident(cx, a)?, block(cx, c)?)))
                    .collect::<Result<_, E>>()?,
                default: block(cx, default)?,
            },
            TTerm::Default => TTerm::Default,
            TTerm::Tail { callee, args } => TTerm::Tail {
                callee: callee.map(&mut |a| ident(cx, a))?,
                args: args
                    .into_iter()
                    .map(
                        |SpreadOr {
                             value: a,
                             is_spread: b,
                         }| {
                            ident(cx, a).map(|c| SpreadOr {
                                value: c,
                                is_spread: b,
                            })
                        },
                    )
                    .collect::<Result<_, E>>()?,
            },
        })
    }
    //    pub fn as_mut<'a>(&'a mut self) -> TTerm<&'a mut B,&'a mut I> where I: Eq + std::hash::Hash{
    //     match self{
    //         TTerm::Return(a) => TTerm::Return(a.as_mut()),
    //         TTerm::Throw(t) => TTerm::Throw(t),
    //         TTerm::Jmp(j) => TTerm::Jmp(j),
    //         TTerm::CondJmp { cond, if_true, if_false } => TTerm::CondJmp { cond, if_true, if_false },
    //         TTerm::Switch { x, blocks, default } => TTerm::Switch { x, blocks: blocks.iter_mut().collect(), default },
    //         TTerm::Default => TTerm::Default,
    //     }
    // }
}
impl<B, I> Default for TTerm<B, I> {
    fn default() -> Self {
        TTerm::Default
    }
}
enum Frame<'a> {
    Assign(&'a AssignTarget, AssignOp),
    Member(&'a MemberProp),
    Member2(&'a MemberProp, &'a MemberProp),
    Call(Vec<&'a Expr>, Vec<&'a Expr>),
    CallMember(&'a MemberProp, Vec<&'a Expr>, Vec<&'a Expr>),
    CallMember2(Vec<&'a Expr>, &'a MemberProp, Vec<&'a Expr>, &'a MemberProp),
    Await,
    Yield {
        delegate: bool,
    },
    Cond {
        thena: &'a Expr,
        elsea: &'a Expr,
        fra: Vec<Frame<'a>>,
        thenb: &'a Expr,
        elseb: &'a Expr,
        frb: Vec<Frame<'a>>,
    },
}
// #[derive(Default)]
