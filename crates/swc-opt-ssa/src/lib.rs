//! Optimized SSA representation with type information.
//!
//! This crate extends the basic SSA form with type information and optimization
//! hints. It introduces an enhanced value representation that tracks types and
//! includes deoptimization points for speculative optimizations.
//!
//! # Optimized SSA
//!
//! The optimized SSA form adds:
//! - Type annotations on values (using `OptType`)
//! - Assertion nodes for type guards
//! - Deoptimization points for speculative optimizations
//! - Emit nodes that can be lowered differently based on type information
//!
//! # Key Types
//!
//! - [`OptValue`]: An optimized SSA value with type information
//! - [`OptFunc`]: A function in optimized SSA form
//! - [`OptCfg`]: The optimized SSA control flow graph
//! - [`OptType`]: Type information for values
//!
//! # Modules
//!
//! - [`impls`]: Trait implementations for optimized SSA types
//! - [`into`]: Conversion from basic SSA to optimized SSA

use std::collections::BTreeSet;
use swc_ecma_ast::Lit;
use swc_ssa::{SCatch, SPostcedent, STarget, STerm, SValue, simplify::SValGetter, sval_item};
use swc_tac::Item;
pub mod impls;
pub mod into;
pub use portal_jsc_swc_util::r#type::{ObjType, OptType};
/// An optimized SSA value with type information and optimization hints.
///
/// This extends basic SSA values with type information and special nodes for
/// optimization. It allows for speculative optimizations with deoptimization
/// fallbacks.
///
/// # Type Parameters
///
/// - `I`: Value identifier type
/// - `B`: Block identifier type
/// - `F`: Function type
/// - `D`: Deoptimizer type
///
/// # Variants
///
/// - `Deopt`: A deoptimization point for speculative optimizations
/// - `Assert`: A type assertion/guard
/// - `Emit`: A value with type information that can be emitted
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum OptValue<I = OptValueId, B = OptBlockId, F = OptFunc, D = ()> {
    /// Deoptimization point - fallback if speculation fails
    Deopt {
        /// The value being deoptimized
        value: I,
        /// The deoptimization strategy
        deoptimizer: D,
    },
    /// Type assertion/guard
    Assert {
        /// The value being asserted
        val: I,
        /// The asserted type (if known)
        ty: Option<OptType>,
    },
    /// A value to emit with type information
    Emit {
        /// The underlying SSA value
        val: SValue<I, B, F>,
        /// The inferred or asserted type
        ty: Option<OptType>,
    },
}
impl<I, B, F, D> OptValue<I, B, F, D> {
    pub fn as_ref(&self) -> OptValue<&I, &B, &F, &D> {
        match self {
            OptValue::Deopt { value, deoptimizer } => OptValue::Deopt { value, deoptimizer },
            OptValue::Assert { val, ty } => OptValue::Assert {
                val,
                ty: ty.clone(),
            },
            OptValue::Emit { val, ty } => OptValue::Emit {
                val: val.as_ref(),
                ty: ty.clone(),
            },
        }
    }
    pub fn as_mut(&mut self) -> OptValue<&mut I, &mut B, &mut F, &mut D> {
        match self {
            OptValue::Deopt { value, deoptimizer } => OptValue::Deopt { value, deoptimizer },
            OptValue::Assert { val, ty } => OptValue::Assert {
                val,
                ty: ty.clone(),
            },
            OptValue::Emit { val, ty } => OptValue::Emit {
                val: val.as_mut(),
                ty: ty.clone(),
            },
        }
    }
    pub fn map<Ctx, E, I2: Ord, B2, F2, D2>(
        self,
        ctx: &mut Ctx,
        i: &mut (dyn FnMut(&mut Ctx, I) -> Result<I2, E> + '_),
        b: &mut (dyn FnMut(&mut Ctx, B) -> Result<B2, E> + '_),
        f: &mut (dyn FnMut(&mut Ctx, F) -> Result<F2, E> + '_),
        d: &mut (dyn FnMut(&mut Ctx, D) -> Result<D2, E> + '_),
    ) -> Result<OptValue<I2, B2, F2, D2>, E> {
        Ok(match self {
            OptValue::Deopt { value, deoptimizer } => OptValue::Deopt {
                value: i(ctx, value)?,
                deoptimizer: d(ctx, deoptimizer)?,
            },
            OptValue::Assert { val, ty } => OptValue::Assert {
                val: i(ctx, val)?,
                ty,
            },
            OptValue::Emit { val, ty } => OptValue::Emit {
                val: val.map(ctx, i, b, f)?,
                ty,
            },
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OptValueW {
    pub value: OptValue,
}

// Define specialized OptValueArena and OptValueId types
swc_ll_common::define_arena!(pub OptValueArena, pub OptValueId for OptValueW);

#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct OptBlock {
    pub params: Vec<(OptValueId, Option<OptType>)>,
    pub insts: Vec<OptValueId>,
    pub postcedent: OptPostcedent,
}

// Define specialized OptBlockArena and OptBlockId types
swc_ll_common::define_arena!(pub OptBlockArena, pub OptBlockId for OptBlock);

pub type OptPostcedent = SPostcedent<OptValueId, OptBlockId>;
pub type OptTarget = STarget<OptValueId, OptBlockId>;
pub type OptTerm = STerm<OptValueId, OptBlockId>;
pub type OptCatch = SCatch<OptValueId, OptBlockId>;
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct OptCfg {
    pub values: OptValueArena,
    pub blocks: OptBlockArena,
    pub decls: BTreeSet<swc_ecma_ast::Id>,
}
impl OptValueW {
    pub fn ty(&self, cfg: &OptCfg) -> Option<OptType> {
        match &self.value {
            OptValue::Deopt { value: d, .. } => {
                let x = cfg.values[*d].ty(cfg);
                x.and_then(|y| y.parent(Default::default()))
            }
            OptValue::Assert { val: _, ty } => ty.clone(),
            OptValue::Emit { val: _, ty } => ty.clone(),
        }
    }
    pub fn constant(&self, cfg: &OptCfg) -> Option<Lit> {
        match &self.value {
            OptValue::Deopt { value: a, .. } => cfg.values[*a].constant(cfg),
            OptValue::Assert { val, ty: _ } => cfg.values[*val].constant(cfg),
            OptValue::Emit { val, ty: _ } => match val {
                SValue::Item { item: i, span: _ } => match i {
                    Item::Lit { lit } => Some(lit.clone()),
                    _ => None,
                },
                _ => None,
            },
        }
    }
}
impl<Ctx: Clone> SValGetter<OptValueId, OptBlockId, OptFunc, Ctx> for OptCfg {
    fn val(&self, id: OptValueId, ctx: Ctx) -> Option<&SValue<OptValueId, OptBlockId, OptFunc>> {
        match &self.values[id].value {
            OptValue::Deopt { value: a, .. } => self.val(*a, ctx),
            OptValue::Assert { val, ty: _ } => self.val(*val, ctx),
            OptValue::Emit { val, ty: _ } => Some(val),
        }
    }
    fn val_mut(
        &mut self,
        id: OptValueId,
        ctx: Ctx,
    ) -> Option<&mut SValue<OptValueId, OptBlockId, OptFunc>> {
        let v: *mut OptValue = &mut self.values[id].value as *mut _;
        //SAFETY: only borrowed once; values are moved before recursing
        match unsafe { &mut *v } {
            OptValue::Deopt { value: a, .. } => {
                let a = *a;
                self.val_mut(a, ctx)
            }
            OptValue::Assert { val, ty: _ } => self.val_mut(*val, ctx),
            OptValue::Emit { val, ty: _ } => Some(val),
        }
    }
}
sval_item!(OptCfg [block OptBlockId]);
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OptFunc {
    pub cfg: OptCfg,
    pub entry: OptBlockId,
    pub is_generator: bool,
    pub is_async: bool,
}
impl OptCfg {
    pub fn add_blockparam(&mut self, k: OptBlockId, ty: Option<OptType>) -> OptValueId {
        let v = self.values.alloc(OptValueW {
            value: OptValue::Emit {
                val: SValue::Param {
                    block: k,
                    idx: self.blocks[k].params.len(),
                    ty: (),
                },
                ty: ty.clone(),
            },
        });
        self.blocks[k].params.push((v, ty));
        v
    }
}
