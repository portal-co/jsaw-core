//! Conversion from JavaScript AST to CFG.
//!
//! This module handles the transformation of SWC's JavaScript AST into
//! control flow graph representation. It processes:
//! - Statements and expressions
//! - Control flow structures (loops, conditionals, try-catch)
//! - Labels and break/continue statements

use cfg_traits::Target;

use crate::*;
pub trait ToCfgCfg {
    type Block: Ord + Copy;
    type SidecarContext;
    fn stmt(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        stmt: &Stmt,
        block: Self::Block,
    ) -> Self::Block;
    fn new_block(&mut self, sidecar: &mut Self::SidecarContext) -> Self::Block;
    fn trap_catch(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        block: Self::Block,
        pat: &Pat,
        catch_block: Self::Block,
    );
    fn jump(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        current: Self::Block,
        target: Self::Block,
        span: Option<Span>,
    );
    fn cond_jmp(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        current: Self::Block,
        cond: &Expr,
        if_true: Self::Block,
        if_false: Self::Block,
        span: Option<Span>,
    );
    fn throw(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        current: Self::Block,
        arg: &Expr,
        span: Option<Span>,
    );
    fn return_(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        current: Self::Block,
        arg: Option<&Expr>,
        span: Option<Span>,
    );
    fn switch(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        current: Self::Block,
        discriminant: &Expr,
        blocks: Vec<(&Expr, Self::Block)>,
        default: Self::Block,
        span: Option<Span>,
    );
}
impl ToCfgCfg for Cfg {
    type Block = BlockId;
    type SidecarContext = ();
    fn stmt(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        stmt: &Stmt,
        block: Self::Block,
    ) -> Self::Block {
        self.blocks[block].stmts.push(stmt.clone());
        block
    }
    fn new_block(&mut self, sidecar: &mut Self::SidecarContext) -> Self::Block {
        self.blocks.alloc(Block {
            stmts: vec![],
            end: End {
                catch: Catch::Throw,
                term: Term::Default,
                orig_span: None,
            },
        })
    }
    fn jump(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        current: Self::Block,
        target: Self::Block,
        span: Option<Span>,
    ) {
        self.blocks[current].end.orig_span = span;
        self.blocks[current].end.term = Term::Jmp(target);
    }
    fn cond_jmp(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        current: Self::Block,
        cond: &Expr,
        if_true: Self::Block,
        if_false: Self::Block,
        span: Option<Span>,
    ) {
        self.blocks[current].end.orig_span = span;
        self.blocks[current].end.term = Term::CondJmp {
            cond: cond.clone(),
            if_true,
            if_false,
        };
    }
    fn throw(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        current: Self::Block,
        arg: &Expr,
        span: Option<Span>,
    ) {
        self.blocks[current].end.orig_span = span;
        self.blocks[current].end.term = Term::Throw(arg.clone());
    }
    fn return_(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        current: Self::Block,
        arg: Option<&Expr>,
        span: Option<Span>,
    ) {
        self.blocks[current].end.orig_span = span;
        self.blocks[current].end.term = Term::Return(arg.cloned());
    }
    fn trap_catch(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        block: Self::Block,
        pat: &Pat,
        catch_block: Self::Block,
    ) {
        self.blocks[block].end.catch = Catch::Jump {
            pat: pat.clone(),
            k: catch_block,
        };
    }
    fn switch(
        &mut self,
        sidecar: &mut Self::SidecarContext,
        current: Self::Block,
        discriminant: &Expr,
        blocks: Vec<(&Expr, Self::Block)>,
        default: Self::Block,
        span: Option<Span>,
    ) {
        self.blocks[current].end.orig_span = span;
        self.blocks[current].end.term = Term::Switch {
            x: discriminant.clone(),
            blocks: blocks.into_iter().map(|(e, b)| (e.clone(), b)).collect(),
            default,
        };
    }
}
/// Loop context information.
///
/// Tracks the break and continue targets for a loop during CFG construction.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Loop<T = BlockId> {
    pub r#break: T,
    pub r#continue: T,
}

pub struct ToCfgConversionCtx<TargetCfg: ToCfgCfg = Cfg> {
    pub catch: Catch<TargetCfg::Block>,
    pub cur_loop: Option<Loop<TargetCfg::Block>>,
    pub labelled: HashMap<Ident, Loop<TargetCfg::Block>>,
}
impl<TargetCfg: ToCfgCfg> Default for ToCfgConversionCtx<TargetCfg> {
    fn default() -> Self {
        Self {
            catch: Catch::Throw,
            cur_loop: None,
            labelled: HashMap::new(),
        }
    }
}
impl<TargetCfg: ToCfgCfg> Clone for ToCfgConversionCtx<TargetCfg> {
    fn clone(&self) -> Self {
        Self {
            catch: self.catch.clone(),
            cur_loop: self.cur_loop,
            labelled: self.labelled.clone(),
        }
    }
}
pub trait ToCfg<TargetCfg: ToCfgCfg = Cfg> {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx<TargetCfg>,
        cfg: &mut TargetCfg,
        sidecar: &mut TargetCfg::SidecarContext,
        // statement: Stmt,
        current: TargetCfg::Block,
        label: Option<Ident>,
    ) -> anyhow::Result<TargetCfg::Block>;
}
impl<T: ToCfg<TargetCfg> + ?Sized, TargetCfg: ToCfgCfg> ToCfg<TargetCfg> for &'_ T {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx<TargetCfg>,
        cfg: &mut TargetCfg,
        sidecar: &mut TargetCfg::SidecarContext,
        // statement: Stmt,
        current: TargetCfg::Block,
        label: Option<Ident>,
    ) -> anyhow::Result<TargetCfg::Block> {
        (**self).transform(ctx, cfg, sidecar, current, label)
    }
}
impl<T: ToCfg<TargetCfg>, TargetCfg: ToCfgCfg> ToCfg<TargetCfg> for Vec<T> {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx<TargetCfg>,
        cfg: &mut TargetCfg,
        sidecar: &mut TargetCfg::SidecarContext,
        // statement: Stmt,
        current: TargetCfg::Block,
        label: Option<Ident>,
    ) -> anyhow::Result<TargetCfg::Block> {
        ctx.transform_all(cfg, sidecar, self, current, label)
    }
}
impl<T: ToCfg<TargetCfg>, TargetCfg: ToCfgCfg> ToCfg<TargetCfg> for [T] {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx<TargetCfg>,
        cfg: &mut TargetCfg,
        sidecar: &mut TargetCfg::SidecarContext,
        // statement: Stmt,
        current: TargetCfg::Block,
        label: Option<Ident>,
    ) -> anyhow::Result<TargetCfg::Block> {
        ctx.transform_all(cfg, sidecar, self, current, label)
    }
}
struct If<'a, TargetCfg: ToCfgCfg = Cfg> {
    span: Span,
    test: &'a Expr,
    cons: &'a (dyn ToCfg<TargetCfg> + 'a),
    alt: Option<&'a (dyn ToCfg<TargetCfg> + 'a)>,
}
struct DoWhile<'a, TargetCfg: ToCfgCfg = Cfg> {
    span: Span,
    test: &'a Expr,
    body: &'a (dyn ToCfg<TargetCfg> + 'a),
}
struct While<'a, TargetCfg: ToCfgCfg = Cfg> {
    span: Span,
    test: &'a Expr,
    body: &'a (dyn ToCfg<TargetCfg> + 'a),
}
impl<TargetCfg: ToCfgCfg> ToCfg<TargetCfg> for DoWhile<'_, TargetCfg> {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx<TargetCfg>,
        cfg: &mut TargetCfg,
        sidecar: &mut TargetCfg::SidecarContext,
        // statement: Stmt,
        current: TargetCfg::Block,
        label: Option<Ident>,
    ) -> anyhow::Result<TargetCfg::Block> {
        let do_while_stmt = self;
        let next = cfg.new_block(sidecar);
        let cont = cfg.new_block(sidecar);
        cfg.jump(sidecar, current, cont, Some(do_while_stmt.span));
        let mut new = ctx.clone();
        new.cur_loop = Some(Loop {
            r#break: next,
            r#continue: cont,
        });
        if let Some(l) = label {
            new.labelled
                .insert(l, new.cur_loop.as_ref().cloned().unwrap());
        }
        let k = new.transform(cfg, sidecar, do_while_stmt.body, cont, None)?;
        cfg.cond_jmp(
            sidecar,
            k,
            &do_while_stmt.test,
            cont,
            next,
            Some(do_while_stmt.span),
        );
        Ok(next)
    }
}
impl<TargetCfg: ToCfgCfg> ToCfg<TargetCfg> for If<'_, TargetCfg> {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx<TargetCfg>,
        cfg: &mut TargetCfg,
        sidecar: &mut TargetCfg::SidecarContext,
        // statement: Stmt,
        current: TargetCfg::Block,
        label: Option<Ident>,
    ) -> anyhow::Result<TargetCfg::Block> {
        let if_stmt = self;
        let span = if_stmt.span;
        let next = cfg.new_block(sidecar);
        let then = cfg.new_block(sidecar);
        let then_end = ctx.transform(
            cfg,
            sidecar,
            if_stmt.cons,
            current,
            match if_stmt.alt.as_ref() {
                None => label,
                Some(_) => None,
            },
        )?;
        cfg.jump(sidecar, then_end, next, None);
        let els = match if_stmt.alt.as_ref() {
            None => then,
            Some(else_stmt) => {
                let els = cfg.new_block(sidecar);
                let els_end = ctx.transform(cfg, sidecar, &**else_stmt, current, None)?;
                cfg.jump(sidecar, els_end, next, None);
                els
            }
        };
        cfg.cond_jmp(sidecar, current, &if_stmt.test, then, els, Some(span));

        Ok(next)
    }
}
impl<TargetCfg: ToCfgCfg> ToCfg<TargetCfg> for While<'_, TargetCfg> {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx<TargetCfg>,
        cfg: &mut TargetCfg,
        sidecar: &mut TargetCfg::SidecarContext,
        // statement: Stmt,
        current: TargetCfg::Block,
        label: Option<Ident>,
    ) -> anyhow::Result<TargetCfg::Block> {
        ctx.transform(
            cfg,
            sidecar,
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
impl<TargetCfg: ToCfgCfg> ToCfg<TargetCfg> for Stmt {
    fn transform(
        &self,
        ctx: &ToCfgConversionCtx<TargetCfg>,
        cfg: &mut TargetCfg,
        sidecar: &mut TargetCfg::SidecarContext,
        // statement: Stmt,
        mut current: TargetCfg::Block,
        label: Option<Ident>,
    ) -> anyhow::Result<TargetCfg::Block> {
        let statement = self;
        if let Stmt::Throw(throw_stmt) = statement {
            cfg.throw(sidecar, current, &throw_stmt.arg, Some(throw_stmt.span()));
            return Ok(cfg.new_block(sidecar));
        }
        if let Stmt::Return(return_stmt) = statement {
            cfg.return_(
                sidecar,
                current,
                return_stmt.arg.as_deref(),
                Some(return_stmt.span()),
            );
            return Ok(cfg.new_block(sidecar));
        }
        if let Stmt::Try(try_stmt) = statement {
            let span = try_stmt.span();
            let next = cfg.new_block(sidecar);
            let catch = match &try_stmt.handler {
                None => None,
                Some(catch_clause) => Some({
                    let catch_block_id = cfg.new_block(sidecar);
                    let catch_end_id = ctx.transform_all(
                        cfg,
                        sidecar,
                        &catch_clause.body.stmts,
                        catch_block_id,
                        None,
                    )?;
                    cfg.jump(sidecar, catch_end_id, next, None);
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
            let try_end_id =
                new.transform_all(cfg, sidecar, &try_stmt.block.stmts, current, None)?;
            cfg.jump(sidecar, try_end_id, next, Some(span));
            let next = match try_stmt.finalizer.as_ref() {
                Some(finalizer) => ctx.transform_all(cfg, sidecar, &finalizer.stmts, next, None)?,
                None => next,
            };
            return Ok(next);
        }
        if let Stmt::Block(block) = statement {
            return ctx.transform_all(cfg, sidecar, &block.stmts, current, None);
        }
        if let Stmt::If(if_stmt) = statement {
            return ctx.transform(
                cfg,
                sidecar,
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
            let next = cfg.new_block(sidecar);
            let mut target = ctx.clone();
            if target.cur_loop.is_none() {
                target.cur_loop = Some(Loop {
                    r#break: next,
                    r#continue: next,
                })
            };
            target.cur_loop.as_mut().unwrap().r#break = next;
            let mut cur = cfg.new_block(sidecar);
            let mut default = next;
            let mut blocks = HashMap::new();
            for case in switch_stmt.cases.iter() {
                match case.test.as_ref() {
                    None => {
                        default = cur;
                        cur = target.transform_all(cfg, sidecar, &case.cons, cur, None)?;
                    }
                    Some(test) => {
                        blocks.insert(&**test, cur);
                        cur = target.transform_all(cfg, sidecar, &case.cons, cur, None)?;
                    }
                }
            }
            cfg.jump(sidecar, current, cur, Some(span));
            cfg.switch(
                sidecar,
                current,
                &switch_stmt.discriminant,
                blocks.into_iter().collect(),
                default,
                Some(span),
            );

            return Ok(next);
        }
        if let Stmt::Break(break_stmt) = statement {
            cfg.jump(
                sidecar,
                current,
                match &break_stmt.label {
                    Some(l) => ctx.labelled.get(l),
                    None => ctx.cur_loop.as_ref(),
                }
                .context("in getting the current loop")?
                .r#break,
                Some(break_stmt.span()),
            );
            return Ok(cfg.new_block(sidecar));
        }
        if let Stmt::Continue(continue_stmt) = statement {
            cfg.jump(
                sidecar,
                current,
                match &continue_stmt.label {
                    Some(l) => ctx.labelled.get(l),
                    None => ctx.cur_loop.as_ref(),
                }
                .context("in getting the current loop")?
                .r#continue,
                Some(continue_stmt.span()),
            );
            return Ok(cfg.new_block(sidecar));
        }
        if let Stmt::Labeled(labeled_stmt) = statement {
            let next = cfg.new_block(sidecar);
            let cont = cfg.new_block(sidecar);
            cfg.jump(sidecar, current, cont, Some(labeled_stmt.span));
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
                sidecar,
                &*labeled_stmt.body,
                cont,
                Some(labeled_stmt.label.clone()),
            )?;
            cfg.jump(sidecar, k, next, None);
            return Ok(next);
        }
        if let Stmt::DoWhile(do_while_stmt) = statement {
            return ctx.transform(
                cfg,
                sidecar,
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
                sidecar,
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
                current = cfg.stmt(
                    sidecar,
                    &match init {
                        swc_ecma_ast::VarDeclOrExpr::VarDecl(var_decl) => {
                            Stmt::Decl(Decl::Var(var_decl))
                        }
                        swc_ecma_ast::VarDeclOrExpr::Expr(expr) => Stmt::Expr(ExprStmt {
                            span: expr.span(),
                            expr,
                        }),
                    },
                    current,
                );
            }
            let true_ = Box::new(Expr::Lit(Lit::Bool(Bool {
                span: for_stmt.span,
                value: true,
            })));
            let up;
            return ctx.transform(
                cfg,
                sidecar,
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
        current = cfg.stmt(sidecar, statement, current);
        Ok(current)
    }
}
impl<TargetCfg: ToCfgCfg> ToCfgConversionCtx<TargetCfg> {
    pub fn transform_all(
        &self,
        cfg: &mut TargetCfg,
        sidecar: &mut TargetCfg::SidecarContext,
        statements: &[impl ToCfg<TargetCfg>],
        mut current: TargetCfg::Block,
        label: Option<Ident>,
    ) -> anyhow::Result<TargetCfg::Block> {
        for statement in statements {
            current = self.transform(cfg, sidecar, statement, current, label.clone())?;
        }
        Ok(current)
    }
    pub fn transform(
        &self,
        cfg: &mut TargetCfg,
        sidecar: &mut TargetCfg::SidecarContext,
        statement: &(dyn ToCfg<TargetCfg> + '_),
        current: TargetCfg::Block,
        label: Option<Ident>,
    ) -> anyhow::Result<TargetCfg::Block> {
        statement.transform(self, cfg, sidecar, current, label)
    }
}
