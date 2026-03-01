//! Compile-time constant evaluation over [`SCfg`] SSA values.
//!
//! This module provides the canonical home for **`eval_const_int`** and the
//! **`ParamEnv`** trait that enables cross-frame parameter propagation.
//!
//! # Status
//!
//! This module is a **implementation guide / forward declaration**.  The
//! working implementation currently lives in
//! `dreamcompiler-lower/src/to_fast_ir/js.rs` as a local copy.  Once this
//! module is fully implemented, `dreamcompiler-lower` should re-export the
//! types from here and delete its local copies.
//!
//! # Design
//!
//! ## `eval_const_int`
//!
//! A bounded backward walk over SSA values that constant-folds:
//!
//! | SSA node                          | Action                                       |
//! |-----------------------------------|----------------------------------------------|
//! | `Item::Lit { Num(n) }`            | return `Some(n as i64)`                      |
//! | `Item::Bin { Add, l, r }`         | `eval(l)? + eval(r)?`  (wrapping)            |
//! | `Item::Bin { Sub, l, r }`         | `eval(l)? - eval(r)?`  (wrapping)            |
//! | `Item::Just { id }`               | follow `id`                                  |
//! | `Assign { val }`                  | follow `val`                                 |
//! | `EdgeBlocker { value }`           | follow `value`                               |
//! | `StoreId { val }`                 | follow `val`                                 |
//! | `Param { block, idx }` with ≥1   | if all predecessors pass the same value,     |
//! |   in-CFG predecessor              | follow that value; else `None`               |
//! | `Param { block, idx }` with zero  | **entry-block param** — delegate to          |
//! |   in-CFG predecessors             | `parent.lookup_param(idx)` (see below)       |
//! | anything else                     | return `None`                                |
//!
//! The loop budget (64 iterations for the main `loop`, plus one recursive
//! call per binary arm) prevents infinite loops on cyclic SSA.
//!
//! ## `ParamEnv` — cross-frame parameter resolution
//!
//! When `eval_const_int` reaches an entry-block `Param` it cannot resolve
//! the value from within the callee's CFG alone.  `ParamEnv` provides the
//! bridge to the caller:
//!
//! ```text
//! outer: calls middle(a, b)
//!   middle: tail-calls inner(1, a, b)           ← `1` is a literal
//!     inner: inlineme_n(n)  where n = Param(0)  ← entry-block param
//! ```
//!
//! When checking whether `inner` is inlinable from `middle`'s context, a
//! `CallSiteParamEnv` is constructed:
//!
//! ```text
//! CallSiteParamEnv {
//!   caller_cfg:  middle's SCfg,
//!   call_args:   [SValueId-for-`1`, SValueId-for-`a`, SValueId-for-`b`],
//!   grandparent: None   // or outer's ParamEnv if needed
//! }
//! ```
//!
//! `eval_const_int(inner.cfg, Param(0), Some(&call_site_env))` hits the
//! entry-param branch, calls `call_site_env.lookup_param(0)`, which calls
//! `eval_const_int(middle.cfg, SValueId-for-`1`, grandparent)`, which
//! immediately returns `Some(1)`.
//!
//! This nesting is bounded by the number of active inlining levels
//! (capped by `MAX_INLINE_DEPTH` in the consumer).
//!
//! # Implementation notes
//!
//! 1. `eval_const_int` is intentionally *arithmetic-only* (Add/Sub).
//!    Extending it to other operators (Mul, BitAnd, …) is straightforward
//!    but not needed for the current `inlineme_n` use-case.
//!
//! 2. Only integer-valued `Lit::Num` nodes are supported.  Floating-point
//!    literals are cast to `i64` (truncating), which is correct for depth
//!    counters but should not be used for general floating-point folding.
//!
//! 3. The `ParamEnv` trait is object-safe (`lookup_param` takes `&self` and
//!    returns a plain `Option<i64>`).  It is intentionally kept minimal so
//!    that it can be stored as `Option<&dyn ParamEnv>` without allocating.
//!
//! 4. `CallSiteParamEnv` holds a `grandparent: Option<&dyn ParamEnv>` so
//!    that chains of three or more inlining levels fold correctly.
//!
//! # Relationship to `dreamcompiler-lower`
//!
//! The working copy in `dreamcompiler-lower/src/to_fast_ir/js.rs` uses the
//! crate-private `portal_jsc_swc_ssa` alias for all types.  When migrating:
//!
//! 1. Implement `eval_const_int` and `ParamEnv` / `CallSiteParamEnv` in
//!    this file (public, exported from the crate root via `pub use eval::*`).
//! 2. Update `dreamcompiler-lower` to import them:
//!    ```rust
//!    use portal_jsc_swc_ssa::eval::{eval_const_int, ParamEnv, CallSiteParamEnv};
//!    ```
//! 3. Delete the local copies in `js.rs`.

use crate::{SCfg, SBlockId, SValueId, SValue};
use swc_tac::{Item, SpreadOr, TCallee};
use swc_ecma_ast::BinaryOp;

// ── Trait ─────────────────────────────────────────────────────────────────────

/// Contextual knowledge about a function's call site, used by
/// [`eval_const_int`] to resolve entry-block parameters to their
/// statically-known caller-side values.
///
/// Each level of the inlining stack that wants to propagate constant
/// arguments downward implements this trait.  At the outermost level
/// (no known call site) the implementor is absent (`None`).
pub trait ParamEnv {
    /// Return the statically-known `i64` value for entry-block parameter
    /// `param_idx` (0-based), or `None` if the value is not a compile-time
    /// constant (or if `param_idx` is out of range for this call site).
    fn lookup_param(&self, param_idx: usize) -> Option<i64>;
}

// ── `CallSiteParamEnv` ────────────────────────────────────────────────────────

/// A [`ParamEnv`] that resolves parameters by evaluating the argument
/// expressions at a specific call site in the *caller's* SSA graph.
///
/// Construct one of these whenever `eval_const_int` or `is_inlinable` is
/// called from a context where the call-site arguments are known (i.e. you
/// are processing an `Item::Call` or `STerm::Tail` node).
pub struct CallSiteParamEnv<'a> {
    /// The caller's CFG — used to evaluate argument expressions.
    pub caller_cfg: &'a SCfg,
    /// The SSA-level arguments passed to the call.  `call_args[i].value` is
    /// a [`SValueId`] in `caller_cfg` whose constant value (if any) maps to
    /// parameter `i` of the callee.
    pub call_args: &'a [SpreadOr<SValueId>],
    /// Parent environment for the caller itself — allows folding through
    /// multiple levels of inlining (e.g. A calls B calls C, where B's
    /// argument to C is itself a parameter of B, whose value at A's call
    /// site is a constant).
    pub grandparent: Option<&'a dyn ParamEnv>,
}

impl ParamEnv for CallSiteParamEnv<'_> {
    fn lookup_param(&self, param_idx: usize) -> Option<i64> {
        let arg_vid = self.call_args.get(param_idx)?.value;
        eval_const_int(self.caller_cfg, arg_vid, self.grandparent)
    }
}

// ── `eval_const_int` ─────────────────────────────────────────────────────────

/// Walk backward through SSA values in `cfg`, constant-folding arithmetic
/// and transparent nodes.  Returns the integer value if fully constant,
/// `None` otherwise.
///
/// See the [module-level documentation](self) for the full folding table and
/// a description of how `parent` enables cross-frame propagation.
pub fn eval_const_int(
    cfg: &SCfg,
    mut vid: SValueId,
    parent: Option<&dyn ParamEnv>,
) -> Option<i64> {
    // Guard against cycles / very deep intra-function chains.
    for _ in 0..64 {
        match &cfg.values[vid].value {
            // ── Identity / transparent nodes ─────────────────────────────────
            SValue::Item { item: Item::Just { id }, .. } => { vid = *id; }
            SValue::Assign { val, .. }                   => { vid = *val; }
            SValue::EdgeBlocker { value, .. }            => { vid = *value; }
            SValue::StoreId { val, .. }                  => { vid = *val; }

            // ── Constant ─────────────────────────────────────────────────────
            SValue::Item { item: Item::Lit { lit: swc_ecma_ast::Lit::Num(n) }, .. } => {
                return Some(n.value as i64);
            }

            // ── Binary: Add or Subtract ───────────────────────────────────────
            SValue::Item {
                item: Item::Bin { left, right, op: BinaryOp::Add },
                ..
            } => {
                let l = eval_const_int(cfg, *left, parent)?;
                let r = eval_const_int(cfg, *right, parent)?;
                return Some(l.wrapping_add(r));
            }
            SValue::Item {
                item: Item::Bin { left, right, op: BinaryOp::Sub },
                ..
            } => {
                let l = eval_const_int(cfg, *left, parent)?;
                let r = eval_const_int(cfg, *right, parent)?;
                return Some(l.wrapping_sub(r));
            }

            // ── Block parameter ───────────────────────────────────────────────
            SValue::Param { block, idx, .. } => {
                // Check whether there are any in-CFG predecessors for this
                // (block, idx) pair.
                let mut intra = cfg.inputs(*block, *idx);
                match intra.next() {
                    // No in-CFG predecessors → entry-block parameter.
                    // Delegate to the parent call-site environment (if any).
                    None => return parent?.lookup_param(*idx),

                    // Exactly one value, or multiple identical values →
                    // follow it as a concrete SSA value within this CFG.
                    Some(only) if intra.all(|v| v == only) => { vid = only; }

                    // Multiple different values → phi-merged; not constant.
                    _ => return None,
                }
            }

            _ => return None,
        }
    }
    None
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    //! Unit tests for `eval_const_int` and `CallSiteParamEnv`.
    //!
    //! # Recommended test cases (to implement once the module is live)
    //!
    //! 1. **Literal**: `Lit::Num(3.0)` → `Some(3)`.
    //!
    //! 2. **Add of two literals**: `3 + 4` → `Some(7)`.
    //!
    //! 3. **Sub chained with Just**: `Just(id) → Bin(Sub, Lit(5), Lit(2))`
    //!    → `Some(3)`.
    //!
    //! 4. **Entry-block param, parent supplies constant**: construct a
    //!    minimal `SCfg` with one block containing a single `Param(block, 0)`
    //!    entry.  Build a `CallSiteParamEnv` whose `call_args[0]` is a
    //!    `Lit::Num(7)` in a caller CFG.  Assert `Some(7)`.
    //!
    //! 5. **Entry-block param, no parent**: same CFG, `parent = None`
    //!    → `None`.
    //!
    //! 6. **Multi-predecessor param, all same**: two `Jmp` edges into block B
    //!    both passing the same `SValueId` for param 0 → fold through it.
    //!
    //! 7. **Multi-predecessor param, different values**: two edges passing
    //!    different `SValueId`s → `None`.
    //!
    //! 8. **Three-level cross-frame chain**: A calls B with literal `2`,
    //!    B tail-calls C passing `param(0) - 1`, C has `inlineme_n(param(0))`.
    //!    With `grandparent` set to A's env, evaluating C's `param(0)` should
    //!    fold to `Some(1)` (= 2 - 1).
    //!
    //! 9. **Cycle guard**: an SSA cycle (e.g. a phi that feeds itself through
    //!    an Add) must not loop forever — the 64-iteration budget terminates
    //!    it with `None`.
    //!
    //! 10. **Non-integer literal**: `Lit::Str("hello")` → `None` (only `Num`
    //!     is supported).
}
