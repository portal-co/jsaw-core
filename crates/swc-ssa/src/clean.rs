//! Dead-branch elimination for SSA functions.
//!
//! [`clean_func`] removes blocks that are unreachable due to burnt
//! (uncompilable) variables or explicit `trim()` sentinel calls, and
//! optionally injects `assume` hints on the surviving branch of every
//! simplified `CondJmp`.
//!
//! # What makes a block burnt?
//!
//! A block is burnt when **any** of its statements matches one of two
//! conditions (checked independently; either is sufficient):
//!
//! 1. **Trim sentinel** — `native_of(s, …) == Some(Native::Trim)`.  The
//!    `trim()` virtual function is the standard polyglot marker: the author
//!    writes it in the branch that is JS-only, and the compiler removes that
//!    branch unconditionally.
//!
//! 2. **Burnt identifier** — `SValue::LoadId(id)` where `is_id_burnt(id)`
//!    returns `true`.  The caller supplies this predicate; a typical
//!    implementation checks membership in a `BTreeSet<swc_ecma_ast::Id>` of
//!    variables whose initialisers could not be compiled.
//!
//! # Assume injection
//!
//! When [`CleanConfig::inject_assumes`] is `true`, each `CondJmp` that is
//! simplified into a `Jmp` receives an extra assumption appended to its
//! **source block** (the block that owned the `CondJmp`).  The assumption
//! takes the form of a synthetic `globalThis['~Natives_assume'](cond)` call
//! (or `globalThis['~Natives_assume'](!cond)` when the true-branch was the
//! burnt one).  Downstream lowering recognises this pattern and converts it
//! to a zero-cost `CoreOp::Assume` hint.
//!
//! Injection into the **source** block is correct because:
//! - `cond` is already defined there — no SSA forward-reference is created.
//! - The target block may have multiple predecessors; injecting there would
//!   fire the hint on every entry, not just the one from this branch.

use std::{collections::BTreeSet, mem::take};

use portal_jsc_common::natives::Native;
use swc_atoms::Atom;
use swc_common::SyntaxContext;
use swc_ecma_ast::{Lit, Str, UnaryOp};
use swc_tac::{Item, ItemGetterExt as _, SpreadOr, TCallee, TTerm, ext::Verbatim};

use crate::{
    SBlockArena, SBlockId, SFunc, SValue, SValueArena, SValueId, SValueW,
    simplify::{SSACtx, SValGetter as _},
};

// ── Public API ────────────────────────────────────────────────────────────────

/// Configuration for [`clean_func`].
#[derive(Debug, Clone, Copy)]
pub struct CleanConfig {
    /// When `true`, a `globalThis['~Natives_assume'](cond_or_not_cond)` call
    /// is appended to the source block of every simplified `CondJmp`.
    pub inject_assumes: bool,
}

/// Remove unreachable blocks from `sfunc` and, optionally, inject `assume`
/// hints.
///
/// `is_id_burnt` is called for each `SValue::LoadId(id)` encountered during
/// the mark phase.  Return `true` to treat that block as burnt.
pub fn clean_func(sfunc: &mut SFunc, is_id_burnt: &dyn Fn(&swc_ecma_ast::Id) -> bool, cfg: CleanConfig) {
    let mut go = true;
    while take(&mut go) {
        // ── Mark ──────────────────────────────────────────────────────────────
        let mut burns: BTreeSet<SBlockId> = BTreeSet::new();
        'mark: for (k, b) in sfunc.cfg.blocks.iter() {
            for &s in &b.stmts {
                let is_trim = matches!(
                    sfunc.cfg.native_of(
                        s,
                        SSACtx { pierce: true, wrapped: &() },
                        &Verbatim,
                    ),
                    Some(Native::Trim)
                );
                let is_burnt_id = matches!(
                    &sfunc.cfg.values[s].value,
                    SValue::LoadId(id) if is_id_burnt(id)
                );
                if is_trim || is_burnt_id {
                    burns.insert(k);
                    go = true;
                    continue 'mark;
                }
            }
        }

        // ── Spread ────────────────────────────────────────────────────────────
        let mut spread = true;
        while take(&mut spread) {
            // Collect assume-injections in a separate Vec to avoid holding a
            // simultaneous mutable borrow on both `blocks` and `values`.
            let mut assume_injections: Vec<(SValueId, SBlockId, bool)> = Vec::new();

            for (k, b) in sfunc.cfg.blocks.iter_mut() {
                b.postcedent.term = match take(&mut b.postcedent.term) {
                    TTerm::CondJmp { cond, if_true, if_false }
                        if burns.contains(&if_true.block) =>
                    {
                        // True-branch burnt → cond was *false* on the live path.
                        if cfg.inject_assumes {
                            assume_injections.push((cond, k, /* negate */ true));
                        }
                        spread = true;
                        go = true;
                        TTerm::Jmp(if_false)
                    }
                    TTerm::CondJmp { cond, if_true, if_false }
                        if burns.contains(&if_false.block) =>
                    {
                        // False-branch burnt → cond was *true* on the live path.
                        if cfg.inject_assumes {
                            assume_injections.push((cond, k, /* negate */ false));
                        }
                        spread = true;
                        go = true;
                        TTerm::Jmp(if_true)
                    }
                    t => t,
                };
                if let TTerm::Jmp(x) = &b.postcedent.term
                    && burns.contains(&x.block)
                {
                    spread = true;
                    go = true;
                    burns.insert(k);
                    b.postcedent.term = TTerm::Default;
                }
            }

            // Apply assume-injections now that the iter_mut borrow is released.
            for (cond, source_block, negate) in assume_injections {
                inject_assume(
                    &mut sfunc.cfg.values,
                    &mut sfunc.cfg.blocks,
                    source_block,
                    cond,
                    negate,
                );
            }
        }

        // ── Erase ─────────────────────────────────────────────────────────────
        for b in burns {
            sfunc.cfg.blocks[b] = Default::default();
        }
    }
}

// ── Assume synthesis ─────────────────────────────────────────────────────────

/// Append a `globalThis['~Natives_assume'](cond_or_not_cond)` call to
/// `source_block`'s statement list.
///
/// When `negate` is `true` a `Un(!)` node is inserted before the call so the
/// assumption reads `assume(!cond)` — signalling that the condition was false
/// on this path.
///
/// The synthesised values are, in order:
/// 1. `v_gt   = LoadId("globalThis")`
/// 2. `v_key  = Lit("~Natives_assume")`
/// 3. `v_not  = Un(!cond)`  ← only when `negate = true`
/// 4. `v_call = Call(v_gt['~Natives_assume'], [inner])`
fn inject_assume(
    values: &mut SValueArena,
    blocks: &mut SBlockArena,
    source_block: SBlockId,
    cond: SValueId,
    negate: bool,
) {
    let v_gt = values.alloc(SValueW {
        value: SValue::LoadId((Atom::new("globalThis"), SyntaxContext::empty())),
    });
    let v_key = values.alloc(SValueW {
        value: SValue::Item {
            item: Item::Lit {
                lit: Lit::Str(Str {
                    span: swc_common::DUMMY_SP,
                    value: Atom::new("~Natives_assume").into(),
                    raw: None,
                }),
            },
            span: None,
        },
    });
    let inner = if negate {
        let v_not = values.alloc(SValueW {
            value: SValue::Item {
                item: Item::Un { arg: cond, op: UnaryOp::Bang },
                span: None,
            },
        });
        blocks[source_block].stmts.push(v_gt);
        blocks[source_block].stmts.push(v_key);
        blocks[source_block].stmts.push(v_not);
        v_not
    } else {
        blocks[source_block].stmts.push(v_gt);
        blocks[source_block].stmts.push(v_key);
        cond
    };
    let v_call = values.alloc(SValueW {
        value: SValue::Item {
            item: Item::Call {
                callee: TCallee::Member { func: v_gt, member: v_key },
                args: vec![SpreadOr { value: inner, is_spread: false }],
            },
            span: None,
        },
    });
    blocks[source_block].stmts.push(v_call);
}
