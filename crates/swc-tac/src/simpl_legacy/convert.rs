use swc_ecma_ast::Ident;

use super::*;
pub trait ConvTacDialect: TacDialect<Tag = Infallible> {}
impl<D: TacDialect<Tag = Infallible>> ConvTacDialect for D {}
pub struct SimplTacConverter<D: ConvTacDialect> {
    pub map: BTreeMap<Id<TSimplBlock<D>>, Id<TBlock>>,
}
impl<D: ConvTacDialect> SimplTacConverter<D> {
    pub fn convert_block(
        &mut self,
        i: &TSimplCfg<D>,
        o: &mut TCfg,
        k: Id<TSimplBlock<D>>,
    ) -> anyhow::Result<Id<TBlock>> {
        loop {
            if let Some(k) = self.map.get(&k) {
                return Ok(*k);
            };
            let mut n = o.blocks.alloc(Default::default());
            self.map.insert(k, n);
            for so in i.blocks[k].stmts.iter() {
                let s;
                (s, n) = self.convert_stmt(i, o, k, n, so)?;
                o.blocks[n].stmts.push(s);
            }
            let t: TTerm = match &i.blocks[k].term {
                TSimplTerm::Return(a) => {
                    let a = self.convert_path(
                        i,
                        o,
                        k,
                        n,
                        &a.0,
                        &i.blocks[k].orig_span.unwrap_or(Span::dummy_with_cmt()),
                    );
                    TTerm::Return(Some(a))
                }
                TSimplTerm::Jmp(id) => TTerm::Jmp(self.convert_block(i, o, *id)?),
                TSimplTerm::CondJmp {
                    cond,
                    if_true,
                    if_false,
                } => TTerm::CondJmp {
                    cond: self.convert_path(
                        i,
                        o,
                        k,
                        n,
                        &cond.0,
                        &i.blocks[k].orig_span.unwrap_or(Span::dummy_with_cmt()),
                    ),
                    if_true: self.convert_block(i, o, *if_true)?,
                    if_false: self.convert_block(i, o, *if_false)?,
                },
                TSimplTerm::Select { scrutinee, cases } => todo!(),
                TSimplTerm::Switch { scrutinee, cases } => TTerm::Switch {
                    x: self.convert_path(
                        i,
                        o,
                        k,
                        n,
                        &scrutinee.0,
                        &i.blocks[k].orig_span.unwrap_or(Span::dummy_with_cmt()),
                    ),
                    blocks: cases
                        .iter()
                        .map(|(scrutinee, k2)| {
                            anyhow::Ok((
                                self.convert_path(
                                    i,
                                    o,
                                    k,
                                    n,
                                    &scrutinee.0,
                                    &i.blocks[k].orig_span.unwrap_or(Span::dummy_with_cmt()),
                                ),
                                self.convert_block(i, o, *k2)?,
                            ))
                        })
                        .collect::<Result<_, _>>()?,
                    default: n,
                },
                TSimplTerm::Default => TTerm::Default,
            };
            o.blocks[n].post.term = t;
        }
    }
    fn convert_path_lid(
        &mut self,
        i: &TSimplCfg<D>,
        o: &mut TCfg,
        k: Id<TSimplBlock<D>>,
        mut n: Id<TBlock>,
        left: &SimplPathId,
        span: &Span,
    ) -> LId {
        match left.keys.last() {
            None => LId::Id {
                id: left.root.clone(),
            },
            Some(k) => {
                let obj =
                    left.keys[..(left.keys.len() - 2)]
                        .iter()
                        .fold(left.root.clone(), |a, b| {
                            let v = o.regs.alloc(());
                            o.decls.insert(v.clone());
                            o.blocks[n].stmts.push(TStmt {
                                left: LId::Id { id: v.clone() },
                                flags: ValFlags::default(),
                                right: Item::Lit {
                                    lit: Lit::Str(Str {
                                        span: *span,
                                        value: b.clone(),
                                        raw: None,
                                    }),
                                },
                                span: *span,
                            });
                            o.blocks[n].stmts.push(TStmt {
                                left: LId::Id { id: v.clone() },
                                flags: ValFlags::default(),
                                right: Item::Mem {
                                    obj: a,
                                    mem: v.clone(),
                                },
                                span: *span,
                            });
                            v
                        });
                let v = o.regs.alloc(());
                o.decls.insert(v.clone());
                o.blocks[n].stmts.push(TStmt {
                    left: LId::Id { id: v.clone() },
                    flags: ValFlags::default(),
                    right: Item::Lit {
                        lit: Lit::Str(Str {
                            span: *span,
                            value: k.clone(),
                            raw: None,
                        }),
                    },
                    span: *span,
                });
                LId::Member { obj, mem: [v] }
            }
        }
    }
    fn convert_path(
        &mut self,
        i: &TSimplCfg<D>,
        o: &mut TCfg,
        k: Id<TSimplBlock<D>>,
        mut n: Id<TBlock>,
        left: &SimplPathId,
        span: &Span,
    ) -> crate::Ident {
        left.keys.iter().fold(left.root.clone(), |a, b| {
            let v = o.regs.alloc(());
            o.decls.insert(v.clone());
            o.blocks[n].stmts.push(TStmt {
                left: LId::Id { id: v.clone() },
                flags: ValFlags::default(),
                right: Item::Lit {
                    lit: Lit::Str(Str {
                        span: *span,
                        value: b.clone(),
                        raw: None,
                    }),
                },
                span: *span,
            });
            o.blocks[n].stmts.push(TStmt {
                left: LId::Id { id: v.clone() },
                flags: ValFlags::default(),
                right: Item::Mem {
                    obj: a,
                    mem: v.clone(),
                },
                span: *span,
            });
            v
        })
    }
    fn convert_stmt(
        &mut self,
        i: &TSimplCfg<D>,
        o: &mut TCfg,
        k: Id<TSimplBlock<D>>,
        mut n: Id<TBlock>,
        TSimplStmt {
            left,
            mark,
            flags,
            right,
            span,
        }: &TSimplStmt<D>,
    ) -> anyhow::Result<(TStmt, Id<TBlock>)> {
        macro_rules! lid {
            ($e:expr) => {
                match $e {
                    left => self.convert_path_lid(i, o, k, n, left, span),
                }
            };
        }
        macro_rules! path {
            ($e:expr) => {
                match $e {
                    left => self.convert_path(i, o, k, n, left, span),
                }
            };
        }
        let left: LId = lid!(left);
        let right: Item = match right {
            SimplItem::Just { id } => Item::Just { id: path!(&id.0) },
            SimplItem::Bin { left, right, op } => Item::Bin {
                left: path!(&left.0),
                right: path!(&right.0),
                op: *op,
            },
            SimplItem::Lit { lit } => Item::Lit { lit: lit.clone() },
            SimplItem::CallStatic { r#fn, args } => Item::Call {
                callee: TCallee::Val(path!(&r#fn.path.0)),
                args: args.iter().map(|a| path!(&a.0)).collect(),
            },
            SimplItem::CallTag { tag, args } => match tag.path {},
            SimplItem::DiscriminantIn { value, ids } => todo!(),
        };
        Ok((
            TStmt {
                left,
                flags: *flags,
                right,
                span: *span,
            },
            n,
        ))
    }
}
