use std::{collections::BTreeMap, convert::Infallible, sync::OnceLock};

use id_arena::Id;
use swc_atoms::Atom;
use swc_common::{Mark, Span, SyntaxContext};
use swc_ecma_ast::Id as Ident;
use swc_tac::{Item, LId, TBlock, TCatch, TCfg, TFunc, TStmt, TTerm, ValFlags};

use crate::{SBlock, SFunc, STarget, STerm, SValue, SValueW};
impl SFunc {
    pub fn try_into_with_prefix(&self, prefix: Atom) -> anyhow::Result<TFunc> {
        let value = self;
        let mut cfg = TCfg::default();
        cfg.decls.extend(value.cfg.decls.iter().cloned());
        let mut rew = Rew {
            blocks: Default::default(),
            ctxt: Default::default(),
            prefix: prefix.clone(),
        };
        let entry = rew.trans(&value, &mut cfg, BlockEntry::Block(value.entry))?;
        let ctxt = rew
            .ctxt
            .get_or_init(|| SyntaxContext::empty().apply_mark(Mark::new()))
            .clone();
        let params = value.cfg.blocks[value.entry]
            .params
            .iter()
            .map(|v| mangle_value(prefix.clone(), ctxt, &value, v.0))
            .collect();
        for (value_id, ts_type) in value.cfg.ts.clone().into_iter() {
            cfg.type_annotations.insert(
                mangle_value(prefix.clone(), ctxt, &value, value_id),
                ts_type,
            );
        }
        cfg.ts_retty = value.cfg.ts_retty.clone();
        cfg.generics = value.cfg.generics.clone();

        Ok(TFunc {
            cfg,
            entry,
            params,
            is_generator: value.is_generator,
            is_async: value.is_async,
            ts_params: value.ts_params.clone(),
        })
    }
}
impl<'a> TryFrom<&'a SFunc> for TFunc {
    type Error = anyhow::Error;

    fn try_from(value: &'a SFunc) -> Result<Self, Self::Error> {
        value.try_into_with_prefix(Default::default())
    }
}
impl TryFrom<SFunc> for TFunc {
    type Error = anyhow::Error;
    fn try_from(value: SFunc) -> Result<Self, Self::Error> {
        TryFrom::try_from(&value)
    }
}
#[derive(Default)]
#[non_exhaustive]
pub struct Rew {
    pub blocks: BTreeMap<BlockEntry, Id<TBlock>>,
    pub ctxt: OnceLock<SyntaxContext>,
    pub prefix: Atom,
}

#[derive(Clone, Ord, PartialEq, PartialOrd, Eq)]
pub enum BlockEntry {
    Block(Id<SBlock>),
    Target(STarget, Option<Ident>),
}
impl Rew {
    pub fn trans(
        &mut self,
        func: &SFunc,
        cfg: &mut TCfg,
        block_entry: BlockEntry,
    ) -> anyhow::Result<Id<TBlock>> {
        let ctxt = self
            .ctxt
            .get_or_init(|| SyntaxContext::empty().apply_mark(Mark::new()))
            .clone();
        loop {
            if let Some(existing_block) = self.blocks.get(&block_entry) {
                return Ok(*existing_block);
            }
            let new_block_id = cfg.blocks.alloc(Default::default());
            self.blocks.insert(block_entry.clone(), new_block_id);
            match &block_entry {
                BlockEntry::Block(block_id) => {
                    let catch_clause = match &func.cfg.blocks[*block_id].postcedent.catch {
                        crate::SCatch::Throw => TCatch::Throw,
                        crate::SCatch::Just { target } => {
                            let error = (
                                Atom::new(format!("{}$error", self.prefix)),
                                Default::default(),
                            );
                            cfg.decls.insert(error.clone());
                            TCatch::Jump {
                                pat: error.clone(),
                                k: self.trans(
                                    func,
                                    cfg,
                                    BlockEntry::Target(target.clone(), Some(error)),
                                )?,
                            }
                        }
                    };
                    cfg.blocks[new_block_id].post.catch = catch_clause;
                    for statement in func.cfg.blocks[*block_id].stmts.iter() {
                        match &func.cfg.values[*statement].value {
                            SValue::Param { block, idx, ty } => todo!(),
                            SValue::Item { item, span } => match item {
                                Item::Just { id } => {}
                                item => {
                                    let item_id = item.as_ref().map2(
                                        &mut (),
                                        &mut |_, value| {
                                            anyhow::Ok(mangle_value(
                                                self.prefix.clone(),
                                                ctxt,
                                                func,
                                                *value,
                                            ))
                                        },
                                        &mut |_, field| {
                                            field.try_into_with_prefix(self.prefix.clone())
                                        },
                                    )?;
                                    cfg.blocks[new_block_id].stmts.push(TStmt {
                                        left: LId::Id {
                                            id: mangle_value(
                                                self.prefix.clone(),
                                                ctxt,
                                                func,
                                                *statement,
                                            ),
                                        },
                                        flags: ValFlags::SSA_LIKE,
                                        right: item_id,
                                        span: span
                                            .clone()
                                            .unwrap_or_else(|| Span::dummy_with_cmt()),
                                    });
                                    cfg.decls.insert(mangle_value(
                                        self.prefix.clone(),
                                        ctxt,
                                        func,
                                        *statement,
                                    ));
                                }
                            },
                            SValue::Assign { target, val } => {
                                let target_id = target.clone().map(&mut |value| {
                                    let mangled =
                                        mangle_value(self.prefix.clone(), ctxt, func, value);
                                    cfg.decls.insert(mangled.clone());
                                    return anyhow::Ok(mangled);
                                })?;
                                cfg.blocks[new_block_id].stmts.push(TStmt {
                                    left: target_id,
                                    flags: Default::default(),
                                    right: Item::Just {
                                        id: mangle_value(self.prefix.clone(), ctxt, func, *val),
                                    },
                                    span: Span::dummy_with_cmt(),
                                });
                            }
                            SValue::LoadId(i) => {
                                cfg.blocks[new_block_id].stmts.push(TStmt {
                                    left: LId::Id {
                                        id: mangle_value(
                                            self.prefix.clone(),
                                            ctxt,
                                            func,
                                            *statement,
                                        ),
                                    },
                                    flags: ValFlags::SSA_LIKE,
                                    right: Item::Just { id: i.clone() },
                                    span: Span::dummy_with_cmt(),
                                });
                                cfg.decls.insert(mangle_value(
                                    self.prefix.clone(),
                                    ctxt,
                                    func,
                                    *statement,
                                ));
                            }
                            SValue::StoreId { target, val } => {
                                cfg.blocks[new_block_id].stmts.push(TStmt {
                                    left: LId::Id { id: target.clone() },
                                    flags: Default::default(),
                                    right: Item::Just {
                                        id: mangle_value(self.prefix.clone(), ctxt, func, *val),
                                    },
                                    span: Span::dummy_with_cmt(),
                                });
                            }
                            SValue::EdgeBlocker { value: v, span } => {
                                // cfg.blocks[new_block_id].stmts.push(TStmt {
                                //     left: LId::Id {
                                //         id: mangle_value(ctxt, func, *statement),
                                //     },
                                //     flags: ValFlags::SSA_LIKE,
                                //     right: Item::Just {
                                //         id: mangle_value(ctxt, func, *v),
                                //     },
                                //     span: span
                                //         .as_ref()
                                //         .cloned()
                                //         .unwrap_or_else(|| Span::dummy_with_cmt()),
                                // });
                            }
                        }
                    }
                    let term = func.cfg.blocks[*block_id].postcedent.term.as_ref().map(
                        &mut *self,
                        &mut |this, starget| {
                            this.trans(func, cfg, BlockEntry::Target(starget.clone(), None))
                        },
                        &mut |this, a| Ok(mangle_value(this.prefix.clone(), ctxt, func, *a)),
                    )?;

                    cfg.blocks[new_block_id].post.term = term;
                }
                BlockEntry::Target(starget, val) => {
                    let stmts = val
                        .iter()
                        .cloned()
                        .chain(
                            starget
                                .args
                                .iter()
                                .map(|b| mangle_value(self.prefix.clone(), ctxt, func, *b)),
                        )
                        .enumerate()
                        .map(|(arg_index, arg_value)| TStmt {
                            left: LId::Id {
                                id: mangle_param(
                                    self.prefix.clone(),
                                    ctxt,
                                    starget.block,
                                    arg_index,
                                ),
                            },
                            flags: Default::default(),
                            right: Item::Just { id: arg_value },
                            span: Span::dummy_with_cmt(),
                        });
                    cfg.blocks[new_block_id].stmts.extend(stmts);
                    let term = swc_tac::TTerm::Jmp(self.trans(
                        func,
                        cfg,
                        BlockEntry::Block(starget.block),
                    )?);
                    cfg.blocks[new_block_id].post.term = term;
                }
            }
        }
    }
}
pub fn mangle_param(
    prefix: Atom,
    ctxt: SyntaxContext,
    block_id: Id<SBlock>,
    index: usize,
) -> Ident {
    (
        Atom::new(format!("{prefix}$k{}p{}", block_id.index(), index)),
        ctxt,
    )
}
pub fn mangle_value(
    prefix: Atom,
    ctxt: SyntaxContext,
    func: &SFunc,
    value_id: Id<SValueW>,
) -> Ident {
    match &func.cfg.values[value_id].value {
        SValue::Param { block, idx, ty } => {
            return mangle_param(prefix, ctxt, *block, *idx);
        }
        SValue::Item {
            item: Item::Just { id },
            span,
        } => mangle_value(prefix, ctxt, func, *id),
        SValue::EdgeBlocker { value, span } => mangle_value(prefix, ctxt, func, *value),
        _ => {
            return (Atom::new(format!("{prefix}$v{}", value_id.index())), ctxt);
        }
    }
}
