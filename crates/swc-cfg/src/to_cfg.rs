//! Conversion from JavaScript AST to CFG.
//!
//! This module handles the transformation of SWC's JavaScript AST into
//! control flow graph representation. It processes:
//! - Statements and expressions
//! - Control flow structures (loops, conditionals, try-catch)
//! - Labels and break/continue statements

use crate::*;

/// Loop context information.
///
/// Tracks the break and continue targets for a loop during CFG construction.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Loop<T = BlockId> {
    pub r#break: T,
    pub r#continue: T,
}
#[derive(Clone, Default)]
pub struct ToCfgConversionCtx {
    pub catch: Catch,
    pub cur_loop: Option<Loop>,
    pub labelled: HashMap<Ident, Loop>,
}
pub trait ToCfg {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx,
        cfg: &mut Cfg,
        // statement: Stmt,
        current: BlockId,
        label: Option<Ident>,
    ) -> anyhow::Result<BlockId>;
}
impl<T: ToCfg + ?Sized> ToCfg for &'_ T {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx,
        cfg: &mut Cfg,
        // statement: Stmt,
        current: BlockId,
        label: Option<Ident>,
    ) -> anyhow::Result<BlockId> {
        (**self).transform(ctx, cfg, current, label)
    }
}
impl<T: ToCfg> ToCfg for Vec<T> {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx,
        cfg: &mut Cfg,
        // statement: Stmt,
        current: BlockId,
        label: Option<Ident>,
    ) -> anyhow::Result<BlockId> {
        ctx.transform_all(cfg, self, current, label)
    }
}
impl<T: ToCfg> ToCfg for &'_ [T] {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx,
        cfg: &mut Cfg,
        // statement: Stmt,
        current: BlockId,
        label: Option<Ident>,
    ) -> anyhow::Result<BlockId> {
        ctx.transform_all(cfg, self, current, label)
    }
}
struct If<'a> {
    span: Span,
    test: &'a Expr,
    cons: &'a (dyn ToCfg + 'a),
    alt: Option<&'a (dyn ToCfg + 'a)>,
}
struct DoWhile<'a> {
    span: Span,
    test: &'a Expr,
    body: &'a (dyn ToCfg + 'a),
}
struct While<'a> {
    span: Span,
    test: &'a Expr,
    body: &'a (dyn ToCfg + 'a),
}
impl ToCfg for DoWhile<'_> {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx,
        cfg: &mut Cfg,
        // statement: Stmt,
        current: BlockId,
        label: Option<Ident>,
    ) -> anyhow::Result<BlockId> {
        let do_while_stmt = self;
        let next = ctx.new_block(cfg);
        let cont = ctx.new_block(cfg);
        cfg.blocks[current].end.orig_span = Some(do_while_stmt.span);
        cfg.blocks[current].end.term = Term::Jmp(cont);
        let mut new = ctx.clone();
        new.cur_loop = Some(Loop {
            r#break: next,
            r#continue: cont,
        });
        if let Some(l) = label {
            new.labelled
                .insert(l, new.cur_loop.as_ref().cloned().unwrap());
        }
        let k = new.transform(cfg, do_while_stmt.body, cont, None)?;
        cfg.blocks[k].end.term = Term::CondJmp {
            cond: do_while_stmt.test.clone(),
            if_true: cont,
            if_false: next,
        };
        Ok(next)
    }
}
impl ToCfg for If<'_> {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx,
        cfg: &mut Cfg,
        // statement: Stmt,
        current: BlockId,
        label: Option<Ident>,
    ) -> anyhow::Result<BlockId> {
        let if_stmt = self;
        let span = if_stmt.span;
        let next = ctx.new_block(cfg);
        let then = ctx.new_block(cfg);
        let then_end = ctx.transform(
            cfg,
            if_stmt.cons,
            current,
            match if_stmt.alt.as_ref() {
                None => label,
                Some(_) => None,
            },
        )?;
        cfg.blocks[then_end].end.term = Term::Jmp(next);
        let els = match if_stmt.alt.as_ref() {
            None => then,
            Some(else_stmt) => {
                let els = ctx.new_block(cfg);
                let els_end = ctx.transform(cfg, &**else_stmt, current, None)?;
                cfg.blocks[els_end].end.term = Term::Jmp(next);
                els
            }
        };
        cfg.blocks[current].end.term = Term::CondJmp {
            cond: if_stmt.test.clone(),
            if_true: then,
            if_false: els,
        };
        cfg.blocks[current].end.orig_span = Some(span);
        Ok(next)
    }
}
impl ToCfg for While<'_> {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx,
        cfg: &mut Cfg,
        // statement: Stmt,
        current: BlockId,
        label: Option<Ident>,
    ) -> anyhow::Result<BlockId> {
        ctx.transform(
            cfg,
            // &Stmt::If(IfStmt {
            //     span: while_stmt.span,
            //     test: while_stmt.test.clone(),
            //     alt: None,
            //     cons: Box::new(Stmt::DoWhile(DoWhileStmt {
            //         span: while_stmt.span,
            //         test: while_stmt.test.clone(),
            //         body: while_stmt.body.clone(),
            //     })),
            // }),
            &If {
                span: self.span,
                alt: None,
                test: self.test,
                cons: &DoWhile {
                    span: self.span,
                    test: self.test,
                    body: &self.body,
                },
            },
            current,
            label,
        )
    }
}
impl ToCfg for Stmt {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx,
        cfg: &mut Cfg,
        // statement: Stmt,
        current: BlockId,
        label: Option<Ident>,
    ) -> anyhow::Result<BlockId> {
        let statement = self;
        if let Stmt::Throw(throw_stmt) = statement {
            cfg.blocks[current].end.orig_span = Some(throw_stmt.span());
            cfg.blocks[current].end.term = Term::Throw(*throw_stmt.arg.clone());
            return Ok(ctx.new_block(cfg));
        }
        if let Stmt::Return(return_stmt) = statement {
            cfg.blocks[current].end.orig_span = Some(return_stmt.span());
            cfg.blocks[current].end.term = Term::Return(return_stmt.arg.as_deref().cloned());
            return Ok(ctx.new_block(cfg));
        }
        if let Stmt::Try(try_stmt) = statement {
            let span = try_stmt.span();
            let next = ctx.new_block(cfg);
            let catch = match &try_stmt.handler {
                None => None,
                Some(catch_clause) => Some({
                    let catch_block_id = ctx.new_block(cfg);
                    let catch_end_id =
                        ctx.transform_all(cfg, &catch_clause.body.stmts, catch_block_id, None)?;
                    cfg.blocks[catch_end_id].end.term = Term::Jmp(next);
                    (
                        catch_clause
                            .param
                            .clone()
                            .unwrap_or(Pat::Ident(BindingIdent {
                                id: Ident::new(
                                    Atom::new("_error"),
                                    catch_clause.span,
                                    SyntaxContext::default(),
                                ),
                                type_ann: None,
                            })),
                        catch_block_id,
                    )
                }),
            };
            let mut new = ctx.clone();
            if let Some((catch_param, catch_block_id)) = catch {
                new.catch = Catch::Jump {
                    pat: catch_param,
                    k: catch_block_id,
                };
            };
            let try_end_id = new.transform_all(cfg, &try_stmt.block.stmts, current, None)?;
            cfg.blocks[try_end_id].end.term = Term::Jmp(next);
            cfg.blocks[try_end_id].end.orig_span = Some(span);
            let next = match try_stmt.finalizer.as_ref() {
                Some(finalizer) => ctx.transform_all(cfg, &finalizer.stmts, next, None)?,
                None => next,
            };
            return Ok(next);
        }
        if let Stmt::Block(block) = statement {
            return ctx.transform_all(cfg, &block.stmts, current, None);
        }
        if let Stmt::If(if_stmt) = statement {
            return ctx.transform(
                cfg,
                &If {
                    span: if_stmt.span,
                    test: &if_stmt.test,
                    cons: &*if_stmt.cons,
                    alt: match if_stmt.alt.as_ref() {
                        None => None,
                        Some(a) => Some(&**a),
                    },
                },
                current,
                label,
            );
        }
        if let Stmt::Switch(switch_stmt) = statement {
            let span = switch_stmt.span();
            let next = ctx.new_block(cfg);
            let mut target = ctx.clone();
            if target.cur_loop.is_none() {
                target.cur_loop = Some(Loop {
                    r#break: next,
                    r#continue: next,
                })
            };
            target.cur_loop.as_mut().unwrap().r#break = next;
            let mut cur = ctx.new_block(cfg);
            let mut default = next;
            let mut blocks = HashMap::new();
            for case in switch_stmt.cases.iter() {
                match case.test.as_ref() {
                    None => {
                        default = cur;
                        cur = target.transform_all(cfg, &case.cons, cur, None)?;
                    }
                    Some(test) => {
                        blocks.insert(*test.clone(), cur);
                        cur = target.transform_all(cfg, &case.cons, cur, None)?;
                    }
                }
            }
            cfg.blocks[cur].end.term = Term::Jmp(next);
            cfg.blocks[current].end.term = Term::Switch {
                x: *switch_stmt.discriminant.clone(),
                blocks,
                default,
            };
            cfg.blocks[current].end.orig_span = Some(span);
            return Ok(next);
        }
        if let Stmt::Break(break_stmt) = statement {
            cfg.blocks[current].end.orig_span = Some(break_stmt.span());
            cfg.blocks[current].end.term = Term::Jmp(
                match &break_stmt.label {
                    Some(l) => ctx.labelled.get(l),
                    None => ctx.cur_loop.as_ref(),
                }
                .context("in getting the current loop")?
                .r#break,
            );
            return Ok(ctx.new_block(cfg));
        }
        if let Stmt::Continue(continue_stmt) = statement {
            cfg.blocks[current].end.orig_span = Some(continue_stmt.span());
            cfg.blocks[current].end.term = Term::Jmp(
                match &continue_stmt.label {
                    Some(l) => ctx.labelled.get(l),
                    None => ctx.cur_loop.as_ref(),
                }
                .context("in getting the current loop")?
                .r#continue,
            );
            return Ok(ctx.new_block(cfg));
        }
        if let Stmt::Labeled(labeled_stmt) = statement {
            let next = ctx.new_block(cfg);
            let cont = ctx.new_block(cfg);
            cfg.blocks[current].end.orig_span = Some(labeled_stmt.span());
            cfg.blocks[current].end.term = Term::Jmp(cont);
            let mut new = ctx.clone();
            new.labelled.insert(
                labeled_stmt.label.clone(),
                Loop {
                    r#break: next,
                    r#continue: cont,
                },
            );
            let k = new.transform(
                cfg,
                &*labeled_stmt.body,
                cont,
                Some(labeled_stmt.label.clone()),
            )?;
            cfg.blocks[k].end.term = Term::Jmp(next);
            return Ok(next);
        }
        if let Stmt::DoWhile(do_while_stmt) = statement {
            return ctx.transform(
                cfg,
                &DoWhile {
                    span: do_while_stmt.span,
                    test: &do_while_stmt.test,
                    body: &*do_while_stmt.body,
                },
                current,
                label,
            );
        }
        if let Stmt::While(while_stmt) = statement {
            return ctx.transform(
                cfg,
                &While {
                    span: while_stmt.span,
                    test: &while_stmt.test,
                    body: &*while_stmt.body,
                },
                current,
                label,
            );
        }
        if let Stmt::For(for_stmt) = statement {
            if let Some(init) = for_stmt.init.as_ref().cloned() {
                cfg.blocks[current].stmts.push(match init {
                    swc_ecma_ast::VarDeclOrExpr::VarDecl(var_decl) => {
                        Stmt::Decl(Decl::Var(var_decl))
                    }
                    swc_ecma_ast::VarDeclOrExpr::Expr(expr) => Stmt::Expr(ExprStmt {
                        span: expr.span(),
                        expr,
                    }),
                });
            }
            let true_ = Box::new(Expr::Lit(Lit::Bool(Bool {
                span: for_stmt.span,
                value: true,
            })));
            let up;
            return ctx.transform(
                cfg,
                // &Stmt::While(WhileStmt {
                //     span: for_stmt.span,
                //     test: for_stmt.test.as_ref().unwrap_or_else(|| &true_),
                //     body: Box::new(Stmt::Block(BlockStmt {
                //         span: for_stmt.span,
                //         ctxt: SyntaxContext::default(),
                //         stmts: vec![for_stmt.body.clone()]
                //             .into_iter()
                //             .chain(
                //                 for_stmt
                //                     .update
                //                     .as_ref()
                //                     .map(|a| {
                //                         Box::new(Stmt::Expr(ExprStmt {
                //                             span: a.span(),
                //                             expr: a.clone(),
                //                         }))
                //                     })
                //                     .into_iter(),
                //             )
                //             .map(|a| *a)
                //             .collect(),
                //     })),
                // }),
                &While {
                    span: for_stmt.span,
                    test: for_stmt.test.as_ref().unwrap_or(&true_),
                    body: &[&*for_stmt.body]
                        .into_iter()
                        .chain(match &for_stmt.update {
                            None => None,
                            Some(e) => {
                                up = Stmt::Expr(ExprStmt {
                                    span: for_stmt.span,
                                    expr: e.clone(),
                                });
                                Some(&up)
                            }
                        })
                        .collect::<Vec<_>>(),
                },
                current,
                label,
            );
        }
        cfg.blocks[current].stmts.push(statement.clone());
        Ok(current)
    }
}
impl ToCfgConversionCtx {
    pub fn new_block(&self, cfg: &mut Cfg) -> BlockId {
        cfg.blocks.alloc(Block {
            stmts: vec![],
            end: End {
                catch: self.catch.clone(),
                term: Term::Default,
                orig_span: None,
            },
        })
    }
    pub fn transform_all(
        &self,
        cfg: &mut Cfg,
        statements: &[impl ToCfg],
        mut current: BlockId,
        label: Option<Ident>,
    ) -> anyhow::Result<BlockId> {
        for statement in statements {
            current = self.transform(cfg, statement, current, label.clone())?;
        }
        Ok(current)
    }
    pub fn transform(
        &self,
        cfg: &mut Cfg,
        statement: &(dyn ToCfg + '_),
        current: BlockId,
        label: Option<Ident>,
    ) -> anyhow::Result<BlockId> {
        statement.transform(self, cfg, current, label)
    }
}
