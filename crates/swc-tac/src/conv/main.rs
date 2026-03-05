use super::*;

/// Converter for transforming CFG to TAC representation.
///
/// This struct maintains the conversion state as it transforms blocks from
/// CFG format (with SWC AST expressions) to TAC format (with simple identifiers).
///
/// # Fields
///
/// - `map`: Mapping from CFG blocks to TAC blocks
/// - `ret_to`: Optional return target for transformation
/// - `recatch`: Exception handler for the current context
/// - `this`: Optional `this` binding identifier
/// - `mapper`: Configuration and utilities for the conversion
#[non_exhaustive]
pub struct ToTACConverter<'a> {
    /// Mapping from CFG block IDs to TAC block IDs
    pub map: BTreeMap<swc_cfg::BlockId, TBlockId>,

    pub core: ToTACConverterCore<'a>,
}
impl ToTACConverter<'_> {
    pub fn trans(
        &mut self,
        i: &Cfg,
        o: &mut TCfg,
        b: swc_cfg::BlockId,
    ) -> anyhow::Result<TBlockId> {
        self.convert_block(i, o, b)
    }
    // Private helper for block/term conversion
    fn convert_block(
        &mut self,
        i: &Cfg,
        o: &mut TCfg,
        b: swc_cfg::BlockId,
    ) -> anyhow::Result<TBlockId> {
        loop {
            if let Some(a) = self.map.get(&b) {
                log::trace!("cfg→tac: CFG block {:?} already mapped → TAC block {:?}", b, a);
                return Ok(*a);
            }
            let t = o.blocks.alloc(TBlock {
                stmts: vec![],
                post: TPostecedent {
                    catch: TCatch::Throw,
                    term: Default::default(),
                    orig_span: i.blocks[b].end.orig_span,
                },
            });
            log::trace!("cfg→tac: converting CFG block {:?} → TAC block {:?}", b, t);
            self.map.insert(b, t);
            if let Catch::Jump { pat, k } = &i.blocks[b].end.catch {
                match pat {
                    Pat::Ident(id) => {
                        let k = self.trans(i, o, *k)?;
                        o.blocks[t].post.catch = TCatch::Jump {
                            pat: id.id.clone().into(),
                            k,
                        };
                    }
                    _ => anyhow::bail!("todo: {}:{}", file!(), line!()),
                }
            }
            let mut t = t;
            for s in i.blocks[b].stmts.iter() {
                t = self.core.stmt(o, t, s)?;
            }
            let term = self.convert_terminator(i, o, b, t)?;
            o.blocks[t].post.term = term;
        }
    }
    // Private helper for terminator conversion
    fn convert_terminator(
        &mut self,
        i: &Cfg,
        o: &mut TCfg,
        b: swc_cfg::BlockId,
        mut t: TBlockId,
    ) -> anyhow::Result<TTerm> {
        match &i.blocks[b].end.term {
            swc_cfg::Term::Return(expr) => match expr {
                None => Ok(TTerm::Return(None)),
                Some(a) => match a {
                    Expr::Call(call) => {
                        let (callee, args, t2) = self.core.convert_call_expr(o, t, call)?;
                        t = t2;
                        Ok(TTerm::Tail { callee, args })
                    }
                    a => {
                        let c;
                        (c, t) = self.core.expr(o, t, a)?;
                        Ok(TTerm::Return(Some(c)))
                    }
                },
            },
            swc_cfg::Term::Throw(expr) => {
                let c;
                (c, t) = self.core.expr(o, t, expr)?;
                Ok(TTerm::Throw(c))
            }
            swc_cfg::Term::Jmp(id) => Ok(TTerm::Jmp(self.trans(i, o, *id)?)),
            swc_cfg::Term::CondJmp {
                cond,
                if_true,
                if_false,
            } => {
                let c;
                (c, t) = self.core.expr(o, t, cond)?;
                Ok(TTerm::CondJmp {
                    cond: c,
                    if_true: self.trans(i, o, *if_true)?,
                    if_false: self.trans(i, o, *if_false)?,
                })
            }
            swc_cfg::Term::Switch { x, blocks, default } => {
                let y;
                (y, t) = self.core.expr(o, t, x)?;
                let mut m2 = HashMap::new();
                for (a, b2) in blocks.iter() {
                    let b2 = self.trans(i, o, *b2)?;
                    let c;
                    (c, t) = self.core.expr(o, t, a)?;
                    m2.insert(c, b2);
                }
                Ok(TTerm::Switch {
                    x: y,
                    blocks: m2.into_iter().collect(),
                    default: self.trans(i, o, *default)?,
                })
            }
            swc_cfg::Term::Default => Ok(TTerm::Default),
        }
    }
}
impl TFunc {
    pub fn try_from_with_mapper(value: &Func, mapper: Mapper<'_>) -> anyhow::Result<Self> {
        log::debug!(
            "converting CFG Func to TFunc: {} params, is_async={}, is_generator={}",
            value.params.len(),
            value.is_async,
            value.is_generator,
        );
        let mut cfg = TCfg::default();
        cfg.regs = LAM::new(mapper.vars.clone());
        let mut conv = ToTACConverter {
            map: BTreeMap::new(),
            core: ToTACConverterCore { mapper },
        };
        let mut entry = conv.trans(&value.cfg, &mut cfg, value.entry)?;
        cfg.ts_retty = value.cfg.ts_retty.clone();
        cfg.generics = value.cfg.generics.clone();
        let mut ts_params = vec![];
        let mut params = if value.params.iter().any(|a| a.pat.is_rest()) {
            // ts_params.extend(value.params.iter().map(|_| None));
            let e2 = cfg.blocks.alloc(Default::default());
            let i = cfg.regs.alloc(());
            let span = value.cfg.blocks[value.entry]
                .end
                .orig_span
                .unwrap_or_else(Span::dummy_with_cmt);
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
