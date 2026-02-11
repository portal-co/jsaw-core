//! Optimization stub framework for SSA.
//!
//! This module provides a framework for implementing optimization passes on
//! SSA form. It handles the boilerplate of traversing the CFG while maintaining
//! SSA invariants.
//!
//! # Optimization Framework
//!
//! The `OptStub` provides:
//! - Block-by-block traversal maintaining mappings
//! - Automatic handling of block parameters
//! - Preservation of control flow structure
//! - Support for value transformations
//!
//! Optimization passes can extend this framework to implement specific
//! transformations while the stub handles the structural details.
//!
//! # Key Type
//!
//! [`OptStub`] - The optimization stub maintaining transformation state

use crate::*;
use portal_jsc_swc_util::SemanticCfg;

/// Optimization stub for SSA transformations.
///
/// Provides a framework for implementing optimization passes on SSA form,
/// handling the traversal and structural transformation while allowing
/// custom logic for value transformations.
pub struct OptStub {
    /// Mapping from input blocks to output blocks
    map: BTreeMap<SBlockId, SBlockId>,
}
impl OptStub {
    fn go(
        &mut self,
        i: &SCfg,
        o: &mut SCfg,
        sematic: &SemanticCfg,
        k: SBlockId,
    ) -> anyhow::Result<SBlockId> {
        loop {
            if let Some(k) = self.map.get(&k) {
                return Ok(*k);
            }
            let l = o.blocks.alloc(Default::default());
            self.map.insert(k, l);
            let baseline: BTreeMap<SValueId, SValueId> = i.blocks[k]
                .params
                .iter()
                .map(|a| (a.0, o.add_blockparam(l)))
                .collect();
            o.blocks[l].postcedent.catch = match &i.blocks[k].postcedent.catch {
                SCatch::Throw => SCatch::Throw,
                SCatch::Just { target } => SCatch::Just {
                    target: STarget {
                        block: self.go(i, o, sematic, target.block)?,
                        args: target
                            .args
                            .iter()
                            .filter_map(|a| baseline.get(a))
                            .cloned()
                            .collect(),
                    },
                },
            };
            let mut variants: BTreeMap<SBlockId, BTreeMap<SValueId, SValueId>> =
                [(l, baseline)].into_iter().collect();
            for ins in i.blocks[k].stmts.iter().cloned() {
                for (a, mut b) in take(&mut variants) {
                    match &i.values[ins].value {
                        v => {
                            let v = v.as_ref().map(
                                self,
                                &mut |_, i| b.get(i).cloned().context("in getting the value"),
                                &mut |s, b| s.go(i, o, sematic, *b),
                                &mut |_, _f| todo!(),
                            )?;
                            let c = o.values.alloc(SValueW { value: v });
                            o.blocks[a].stmts.push(c);
                            b.insert(ins, c);
                            variants.insert(a, b);
                        }
                    }
                }
            }
            for (var, baseline) in variants.into_iter() {
                macro_rules! tgt {
                    ($e:expr) => {
                        match $e {
                            target => STarget {
                                block: self.go(i, o, sematic, target.block)?,
                                args: target
                                    .args
                                    .iter()
                                    .filter_map(|a| baseline.get(a))
                                    .cloned()
                                    .collect(),
                            },
                        }
                    };
                }
                o.blocks[var].postcedent.term = i.blocks[k].postcedent.term.as_ref().map(
                    &mut (),
                    &mut |_, target| Ok(tgt!(target)),
                    &mut |_, a| baseline.get(a).cloned().context("in getting the value"),
                )?;
            }
        }
    }
}
