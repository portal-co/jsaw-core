//! Static Single Assignment (SSA) form intermediate representation.
//!
//! This crate provides an SSA form representation for JavaScript/ECMAScript code,
//! which is a lower-level IR than TAC (Three-Address Code) that enforces stronger
//! invariants for optimization.
//!
//! # Static Single Assignment Form
//!
//! In SSA form:
//! - Each variable is assigned exactly once (static single assignment)
//! - Variables are versioned when they would be reassigned in non-SSA form
//! - Control flow merges use block parameters instead of φ-functions
//! - Enables more powerful dataflow analysis and optimizations
//!
//! # Block Parameters Instead of Phi Nodes
//!
//! This SSA representation uses **block parameters** instead of traditional φ-functions.
//! Basic blocks take parameters just like functions, and predecessors pass arguments
//! when jumping to them. This approach:
//! - Makes SSA construction and transformation easier to reason about
//! - Avoids edge cases that occur with φ-nodes (e.g., critical edges)
//! - Provides a cleaner representation for optimization passes
//! - Naturally handles multiple values being merged at the same point
//!
//! For example, instead of:
//! ```text
//! block:
//!   x = φ(x1 from pred1, x2 from pred2)
//! ```
//!
//! We use:
//! ```text
//! block(x):        // x is a block parameter
//!   ...
//! pred1:
//!   jump block(x1) // pass x1 as argument
//! pred2:
//!   jump block(x2) // pass x2 as argument
//! ```
//!
//! # Key Types
//!
//! - [`SFunc`]: A function in SSA form
//! - [`SCfg`]: The SSA control flow graph
//! - [`SBlock`]: A basic block with parameters (replacing φ-functions)
//! - [`SValue`]: An SSA value (operation, parameter, load, store, etc.)
//! - [`SValueW`]: A wrapper around `SValue` for arena storage
//! - [`STerm`]: Block terminator with target blocks and arguments
//! - [`STarget`]: A jump target (block + arguments for its parameters)
//!
//! # Conversion from TAC
//!
//! The primary entry point is converting from TAC to SSA form. This involves:
//! 1. Identifying variables that need versioning
//! 2. Creating block parameters at control flow merges (instead of φ-functions)
//! 3. Threading SSA values through the control flow graph
//! 4. Converting assignments to SSA form
//! 5. Passing appropriate arguments when jumping to blocks
//!
//! # Modules
//!
//! - [`consts`]: Constant propagation in SSA form
//! - [`conv`]: Conversion from TAC to SSA
//! - [`impls`]: Trait implementations for SSA types
//! - [`opt_stub`]: Optimization stub/framework
//! - [`rew`]: Rewriting passes
//! - [`simplify`]: Simplification passes

use anyhow::Context;
use cfg_traits::Term;
use id_arena::{Arena, Id};
use portal_jsc_common::syntax::Asm;
use portal_jsc_swc_util::SemanticCfg;
use ssa_traits::HasChainableValues;
use swc_ecma_visit::Visit;
use std::{
    collections::{BTreeMap, BTreeSet},
    convert::Infallible,
    iter::{empty, once},
    mem::take,
    sync::Arc,
};
use swc_common::Span;
use swc_ecma_ast::{Id as Ident, Lit, TsType, TsTypeAnn, TsTypeParamDecl, UnaryOp};
use swc_tac::{
    Item, TBlock, TCallee, TCfg, TFunc, TStmt, TTerm, ValFlags,
    lam::{AtomResolver, DefaultAtomResolver}, mapped,
};
use swc_tac::{LId, inlinable};
pub mod consts;
// pub mod idw;
pub mod conv;
pub mod impls;
pub mod opt_stub;
pub mod rew;
pub mod simplify;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
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
/// A function in Static Single Assignment (SSA) form.
///
/// Represents a complete function with its SSA control flow graph. Unlike TAC,
/// all values in SSA form are assigned exactly once, and control flow merges
/// are handled explicitly through block parameters.
///
/// # Fields
///
/// - `cfg`: The SSA control flow graph containing all blocks and values
/// - `entry`: The entry block identifier
/// - `is_generator`: Whether this is a generator function
/// - `is_async`: Whether this is an async function
/// - `ts_params`: Optional TypeScript type annotations for parameters
#[derive(Clone, Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct SFunc {
    /// The SSA control flow graph
    pub cfg: SCfg,
    /// The entry block (where execution begins)
    pub entry: Id<SBlock>,
    /// Whether this is a generator function (function*)
    pub is_generator: bool,
    /// Whether this is an async function
    pub is_async: bool,
    /// Optional TypeScript type annotations for parameters
    pub ts_params: Vec<Option<TsType>>,
}
impl TryFrom<TFunc> for SFunc {
    type Error = anyhow::Error;
    fn try_from(value: TFunc) -> Result<Self, Self::Error> {
        TryFrom::try_from(&value)
    }
}
/// The SSA control flow graph for a function.
///
/// Contains all basic blocks and SSA values for a function. Unlike TAC's TCfg,
/// this uses a value arena where each value has a unique ID and is referenced
/// by other values and block terminators.
///
/// # Fields
///
/// - `blocks`: Arena of all basic blocks in the function
/// - `values`: Arena of all SSA values (operations, parameters, etc.)
/// - `ts`: TypeScript type annotations for SSA values
/// - `decls`: Set of declared variables (for non-SSA variables)
/// - `generics`: Optional generic type parameters
/// - `ts_retty`: Optional TypeScript return type annotation
/// - `resolver`: Atom resolver for generating fresh variable names
#[derive(Clone, Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct SCfg {
    /// Arena containing all basic blocks
    pub blocks: Arena<SBlock>,
    /// Arena containing all SSA values
    pub values: Arena<SValueW>,
    /// TypeScript type annotations for values
    pub ts: BTreeMap<Id<SValueW>, TsType>,
    /// Set of declared variables (may be accessed non-SSA style)
    pub decls: BTreeSet<Ident>,
    /// Generic type parameters (if this is a generic function)
    pub generics: Option<TsTypeParamDecl>,
    /// TypeScript return type annotation
    pub ts_retty: Option<TsTypeAnn>,
    /// Atom resolver for generating fresh identifiers
    pub resolver: Arc<dyn AtomResolver>,
}
impl Default for SCfg {
    fn default() -> Self {
        Self {
            blocks: Default::default(),
            values: Default::default(),
            ts: Default::default(),
            decls: Default::default(),
            generics: Default::default(),
            ts_retty: Default::default(),
            resolver: Arc::new(DefaultAtomResolver::default()),
        }
    }
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
    pub fn taints_object(&self, value_id: &Id<SValueW>) -> bool {
        return self.blocks.iter().any(|block_entry| {
            block_entry.1.stmts.iter().any(|stmt_id| {
                let mut current_value = *stmt_id;
                loop {
                    return match &self.values[current_value].value {
                        SValue::Assign { target, val } => target.taints_object(value_id),
                        SValue::Item { item, span } => item.taints_object(value_id),
                        SValue::Param { block, idx, ty } => match self.input(*block, *idx) {
                            None => true,
                            Some(input_value) => {
                                current_value = input_value;
                                continue;
                            }
                        },
                        _ => true,
                    };
                }
            }) || block_entry.1.postcedent.term.taints_object(value_id)
        });
    }
    pub fn refs(&self) -> BTreeSet<Ident> {
        return self
            .values
            .iter()
            .flat_map(|(_value_id, value_wrapper)| match &value_wrapper.value {
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
            .filter(|ident| !self.decls.contains(&*ident))
            .collect();
    }
}
/// An SSA basic block with parameters.
///
/// Unlike TAC blocks which only contain statements, SSA blocks have parameters
/// that replace traditional φ-functions. When control flow jumps to this block
/// from different predecessors, each predecessor provides arguments that are
/// bound to these parameters.
///
/// This design makes SSA construction and transformation easier by avoiding the
/// edge cases that occur with φ-nodes, such as critical edges and the ordering
/// of φ-functions at block entry.
///
/// # Structure
///
/// ```text
/// Block(param1, param2, ...):    // Parameters replace φ-functions
///   stmt1
///   stmt2
///   ...
///   terminator(target_block(arg1, arg2, ...))
/// ```
///
/// # Fields
///
/// - `params`: Block parameters (replace φ-functions for merging values)
/// - `stmts`: SSA value computations in this block
/// - `postcedent`: Terminator specifying control flow and exception handling
#[derive(Default, Clone, Debug, PartialEq, Eq, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct SBlock {
    /// Block parameters (each is an SSA value ID with metadata)
    pub params: Vec<(Id<SValueW>, ())>,
    /// SSA values computed in this block (references into the value arena)
    pub stmts: Vec<Id<SValueW>>,
    /// Block terminator and exception handler
    pub postcedent: SPostcedent,
}
/// The postcedent (exit point) of an SSA basic block.
///
/// Similar to TAC's `TPostcedent`, but with SSA-specific semantics where
/// block targets include arguments for the target block's parameters.
///
/// # Type Parameters
///
/// - `I`: SSA value identifier type (defaults to `Id<SValueW>`)
/// - `B`: Block identifier type (defaults to `Id<SBlock>`)
///
/// # Fields
///
/// - `term`: Normal control flow terminator with target blocks
/// - `catch`: Exception handler specification
#[derive(Clone, Debug, PartialEq, Eq, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct SPostcedent<I = Id<SValueW>, B = Id<SBlock>> {
    /// Normal control flow terminator
    pub term: STerm<I, B>,
    /// Exception handler
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
/// An SSA value representing a computation, parameter, or memory operation.
///
/// Each `SValue` represents a single value in the SSA form. Values are stored
/// in an arena and referenced by their ID. Most values compute something based
/// on other SSA value IDs.
///
/// # Type Parameters
///
/// - `I`: SSA value identifier type (defaults to `Id<SValueW>`)
/// - `B`: Block identifier type (defaults to `Id<SBlock>`)
/// - `F`: Function type (defaults to `SFunc`)
///
/// # Variants
///
/// - `Param`: A block parameter (φ-function input)
/// - `Item`: A computation/operation from the TAC `Item` type
/// - `Assign`: An assignment to a left-hand side location
/// - `LoadId`: Load a non-SSA variable by name
/// - `StoreId`: Store to a non-SSA variable by name
/// - `EdgeBlocker`: A temporary barrier for managing SSA construction on edges
#[derive(Clone, Debug, PartialEq, Eq, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
#[non_exhaustive]
pub enum SValue<I = Id<SValueW>, B = Id<SBlock>, F = SFunc> {
    /// A block parameter (bound when jumping to the block)
    Param {
        /// The block this parameter belongs to
        block: B,
        /// The parameter index within the block
        idx: usize,
        /// Type metadata (currently unused)
        ty: (),
    },
    /// A computed value/operation
    Item {
        /// The operation or value
        item: Item<I, F>,
        /// Source location for debugging
        span: Option<Span>,
    },
    /// An assignment to a location (member, private field, etc.)
    Assign {
        /// The target location
        target: LId<I>,
        /// The value being assigned
        val: I,
    },
    /// Load a variable by name (for non-SSA variables)
    LoadId(Ident),
    /// Store to a variable by name (for non-SSA variables)
    StoreId {
        /// The variable name
        target: Ident,
        /// The value being stored
        val: I,
    },
    /// Temporary edge blocker used during SSA construction
    EdgeBlocker {
        /// The underlying value
        value: I,
        /// Source location
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
    pub fn will_store(&self, id: &Ident) -> bool {
        match self {
            SValue::StoreId { target, val } if target == id => true,
            SValue::Item { item, span } if item.will_store(id) => true,
            _ => false,
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
/// A wrapper around `SValue` for storage in an arena.
///
/// This newtype wrapper allows the value arena to store `SValue` instances
/// with a unique ID. The `#[repr(transparent)]` ensures there's no overhead
/// from the wrapper.
#[repr(transparent)]
#[derive(Clone, Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct SValueW {
    /// The wrapped SSA value
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
/// Exception handler specification for SSA blocks.
///
/// Similar to TAC's `TCatch`, but uses `STarget` to pass the exception value
/// as an argument to the catch block's parameter.
///
/// # Type Parameters
///
/// - `I`: SSA value identifier type (defaults to `Id<SValueW>`)
/// - `B`: Block identifier type (defaults to `Id<SBlock>`)
#[derive(Clone, Debug, PartialEq, Eq, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
#[non_exhaustive]
pub enum SCatch<I = Id<SValueW>, B = Id<SBlock>> {
    /// No exception handler - propagate to caller
    Throw,
    /// Jump to catch handler with exception as argument
    Just {
        /// Target block and arguments (exception value)
        target: STarget<I, B>,
    },
}
impl<I, B> Default for SCatch<I, B> {
    fn default() -> Self {
        Self::Throw
    }
}
/// A jump target in SSA form, consisting of a block and arguments.
///
/// In SSA form, when jumping to a block, we must provide values for all of
/// that block's parameters. This struct packages the target block ID with
/// the argument values.
///
/// # Type Parameters
///
/// - `I`: SSA value identifier type (defaults to `Id<SValueW>`)
/// - `B`: Block identifier type (defaults to `Id<SBlock>`)
///
/// # Fields
///
/// - `block`: The target block identifier
/// - `args`: Values to bind to the target block's parameters
///
/// # Example
///
/// ```text
/// // Jump to block 5 with arguments [v1, v2]
/// STarget { block: 5, args: vec![v1, v2] }
/// ```
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
pub struct STarget<I = Id<SValueW>, B = Id<SBlock>> {
    /// The target block to jump to
    pub block: B,
    /// Arguments to pass to the block's parameters
    pub args: Vec<I>,
}

/// A block terminator in SSA form.
///
/// This is a type alias for `TTerm` (from TAC) but parameterized with `STarget`
/// instead of plain block IDs. This allows each branch to carry arguments for
/// the target block's parameters, which is essential for SSA form.
///
/// All the variants from `TTerm` are available:
/// - `Return`: Return from function
/// - `Throw`: Throw exception
/// - `Jmp`: Unconditional jump with arguments
/// - `CondJmp`: Conditional branch with arguments for both targets
/// - `Switch`: Multi-way branch with arguments for each case
/// - `Tail`: Tail call
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
    pub fn add_blockparam(&mut self, block_id: Id<SBlock>) -> Id<SValueW> {
        let val = SValue::Param {
            block: block_id,
            idx: self.blocks[block_id].params.len(),
            ty: (),
        };
        let val = self.values.alloc(val.into());
        self.blocks[block_id].params.push((val, ()));
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
            if let Some(v) = v.value.const_in(semantic, self, true, ()) {
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
struct TestVisitor;
impl Visit for TestVisitor{
    fn visit_function(&mut self, node: &swc_ecma_ast::Function) {
        
        let tfunc = TFunc::try_from(node.clone()).unwrap();
     
        SFunc::try_from(tfunc).unwrap();
    }
}
#[cfg(test)]
mod tests{
    use swc_ecma_visit::VisitWith;

    use crate::TestVisitor;

    portal_solutions_swibb::simple_module_test!(test_conv ["
    export function foo(a, b){
    return a + b 
    }
    "] => |sm,module|{
     
        module.visit_with(&mut TestVisitor);
    });
}