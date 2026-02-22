use swc_cfg::to_cfg::{ToCfgCfg, ToCfgConversionCtx};

use super::*;
pub struct LiveConverter<'a> {
    pub core: ToTACConverterCore<'a>,
}
impl<'a> ToCfgCfg<LiveConverter<'a>> for TCfg {
    type Block = TBlockId;
    type Error = anyhow::Error;

    fn stmt(
        &mut self,
        sidecar: &mut LiveConverter<'a>,
        stmt: &Stmt,
        block: Self::Block,
    ) -> Result<Self::Block, Self::Error> {
        sidecar.core.stmt(self, block, stmt)
    }

    fn new_block(&mut self, sidecar: &mut LiveConverter<'a>) -> Result<Self::Block, Self::Error> {
        Ok(self.blocks.alloc(Default::default()))
    }

    fn trap_catch(
        &mut self,
        sidecar: &mut LiveConverter<'a>,
        block: Self::Block,
        pat: &Pat,
        catch_block: Self::Block,
    ) -> Result<(), Self::Error> {
        match pat {
            Pat::Ident(pat) => {
                self.blocks[block].post.catch = TCatch::Jump {
                    pat: pat.to_id(),
                    k: catch_block,
                }
            }
            _ => todo!(),
        }
        Ok(())
    }

    fn jump(
        &mut self,
        sidecar: &mut LiveConverter<'a>,
        current: Self::Block,
        target: Self::Block,
        span: Option<Span>,
    ) -> Result<(), Self::Error> {
        self.blocks[current].post.term = TTerm::Jmp(target);
        self.blocks[current].post.orig_span = span;
        Ok(())
    }

    fn cond_jmp(
        &mut self,
        sidecar: &mut LiveConverter<'a>,
        current: Self::Block,
        cond: &Expr,
        if_true: Self::Block,
        if_false: Self::Block,
        span: Option<Span>,
    ) -> Result<(), Self::Error> {
        let (cond, current) = sidecar.core.expr(self, current, cond)?;
        self.blocks[current].post.term = TTerm::CondJmp {
            cond,
            if_true,
            if_false,
        };
        self.blocks[current].post.orig_span = span;
        Ok(())
    }

    fn throw(
        &mut self,
        sidecar: &mut LiveConverter<'a>,
        current: Self::Block,
        arg: &Expr,
        span: Option<Span>,
    ) -> Result<(), Self::Error> {
        let (arg, current) = sidecar.core.expr(self, current, arg)?;
        self.blocks[current].post.term = TTerm::Throw(arg);
        self.blocks[current].post.orig_span = span;
        Ok(())
    }

    fn return_(
        &mut self,
        sidecar: &mut LiveConverter<'a>,
        current: Self::Block,
        arg: Option<&Expr>,
        span: Option<Span>,
    ) -> Result<(), Self::Error> {
        let (arg, current) = match arg {
            Some(expr) => {
                let (arg, current) = sidecar.core.expr(self, current, expr)?;
                (Some(arg), current)
            }
            None => (None, current),
        };
        self.blocks[current].post.term = TTerm::Return(arg);
        self.blocks[current].post.orig_span = span;
        Ok(())
    }

    fn switch(
        &mut self,
        sidecar: &mut LiveConverter<'a>,
        current: Self::Block,
        discriminant: &Expr,
        blocks: Vec<(&Expr, Self::Block)>,
        default: Self::Block,
        span: Option<Span>,
    ) -> Result<(), Self::Error> {
        let (discriminant, mut current) = sidecar.core.expr(self, current, discriminant).unwrap();
        let mut blocks_map = Vec::new();
        for (expr, block) in blocks {
            let id;
            (id, current) = sidecar.core.expr(self, current, expr)?;
            blocks_map.push((id, block));
        }
        self.blocks[current].post.term = TTerm::Switch {
            x: discriminant,
            blocks: blocks_map,
            default,
        };
        self.blocks[current].post.orig_span = span;
        Ok(())
    }
}
impl TFunc {
    pub fn try_from_direct_with_mapper(
        value: &Function,
        mapper: Mapper<'_>,
    ) -> anyhow::Result<Self> {
        let mut cfg = TCfg::default();
        cfg.regs = LAM::new(mapper.vars.clone());
        let mut conv = LiveConverter {
            core: ToTACConverterCore { mapper },
        };
        let mut entry = cfg.blocks.alloc(Default::default());
        let exit = ToCfgConversionCtx::default().transform_all(
            &mut cfg,
            &mut conv,
            value.body.as_ref().map(|a| &*a.stmts).unwrap_or(&[]),
            entry,
            None,
        );
        // cfg.ts_retty = value.cfg.ts_retty.clone();
        // cfg.generics = value.cfg.generics.clone();
        let mut ts_params = vec![];
        let mut params = if value.params.iter().any(|a| a.pat.is_rest()) {
            // ts_params.extend(value.params.iter().map(|_| None));
            let e2 = cfg.blocks.alloc(Default::default());
            let i = cfg.regs.alloc(());
            let span = value.span;
            cfg.blocks[e2].stmts.push(TStmt {
                left: LId::Id { id: i.clone() },
                flags: ValFlags::SSA_LIKE,
                right: Item::Arguments,
                span,
            });
            let k = conv.core.bind_array_contents(
                &mut cfg,
                e2,
                value.params.iter().map(|a| &a.pat).map(Some).collect(),
                &span,
                i.clone(),
                true,
            )?;
            cfg.blocks[k].post.term = TTerm::Jmp(entry);
            entry = e2;
            Default::default()
        } else {
            value
                .params
                .iter()
                .rev()
                .map(|x| {
                    Ok(match &x.pat {
                        Pat::Ident(i) => {
                            ts_params.push(i.type_ann.as_ref().map(|a| (*a.type_ann).clone()));
                            i.id.clone().into()
                        }
                        p => {
                            ts_params.push(None);
                            let e2 = cfg.blocks.alloc(Default::default());
                            let i = cfg.regs.alloc(());
                            let k = conv.core.bind(&mut cfg, e2, p, i.clone(), true)?;
                            cfg.blocks[k].post.term = TTerm::Jmp(entry);
                            entry = e2;
                            i
                        }
                    })
                })
                .collect::<anyhow::Result<Vec<Ident>>>()?
        };
        params.reverse();
        ts_params.reverse();
        Ok(Self {
            cfg,
            entry,
            params,
            is_generator: value.is_generator,
            is_async: value.is_async,
            ts_params,
        })
    }
}
