//! CFG restructuring and reconstruction.
//!
//! This module provides functionality to restructure and rebuild control flow graphs,
//! typically used for transformations that need to create a new CFG from an existing one.

use crate::{Block, Catch, Cfg, Term, to_cfg::ToCfgConversionCtx};
use id_arena::Id;
use std::collections::{BTreeMap, HashMap};

/// CFG restructuring state.
///
/// Maintains mapping from input blocks to output blocks during CFG reconstruction.
#[derive(Default)]
pub struct Recfg {
    pub map: BTreeMap<Id<Block>, Id<Block>>,
}
impl Recfg {
    pub fn go(
        &mut self,
        input_cfg: &Cfg,
        output_cfg: &mut Cfg,
        block_id: Id<Block>,
    ) -> anyhow::Result<Id<Block>> {
        loop {
            if let Some(existing_block_id) = self.map.get(&block_id) {
                return Ok(*existing_block_id);
            }
            let new_block_id = output_cfg.blocks.alloc(Default::default());
            output_cfg.blocks[new_block_id].end.orig_span =
                input_cfg.blocks[block_id].end.orig_span.clone();
            self.map.insert(block_id, new_block_id);
            let catch = match &input_cfg.blocks[block_id].end.catch {
                crate::Catch::Throw => Catch::Throw,
                crate::Catch::Jump { pat, k: target_block } => Catch::Jump {
                    pat: pat.clone(),
                    k: self.go(input_cfg, output_cfg, *target_block)?,
                },
            };
            output_cfg.blocks[new_block_id].end.catch = catch.clone();
            let ctx = ToCfgConversionCtx {
                catch,
                ..Default::default()
            };
            let new_block_id = ctx.transform_all(
                output_cfg,
                &input_cfg.blocks[block_id].stmts.clone(),
                new_block_id,
                None,
            )?;
            let term = match &input_cfg.blocks[block_id].end.term {
                crate::Term::Jmp(id) => Term::Jmp(self.go(input_cfg, output_cfg, *id)?),
                crate::Term::CondJmp {
                    cond,
                    if_true,
                    if_false,
                } => Term::CondJmp {
                    cond: cond.clone(),
                    if_true: self.go(input_cfg, output_cfg, *if_true)?,
                    if_false: self.go(input_cfg, output_cfg, *if_false)?,
                },
                crate::Term::Switch { x, blocks, default } => Term::Switch {
                    x: x.clone(),
                    blocks: blocks
                        .iter()
                        .map(|(case_value, case_block)| Ok((case_value.clone(), self.go(input_cfg, output_cfg, *case_block)?)))
                        .collect::<anyhow::Result<HashMap<_, _>>>()?,
                    default: self.go(input_cfg, output_cfg, *default)?,
                },
                other_term => other_term.clone(),
            };
            output_cfg.blocks[new_block_id].end.term = term;
        }
    }
}
