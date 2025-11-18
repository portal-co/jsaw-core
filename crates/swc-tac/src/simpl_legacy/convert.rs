//! Conversion between TAC and Simpl dialect.
//!
//! This module handles bidirectional conversion between TAC (Three-Address Code)
//! and the Simpl JavaScript dialect. It translates TAC operations into Simpl
//! AST constructs and vice versa.

use super::*;
use std::ops::Deref;
use swc_ecma_ast::Ident;

/// Trait for TAC dialects compatible with Simpl conversion.
pub trait ConvTacDialect: TacDialect<Tag = Infallible> {}
impl<D: TacDialect<Tag = Infallible>> ConvTacDialect for D {}

/// Converter from Simpl TAC to standard TAC.
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
                TSimplTerm::Select { scrutinee, cases } => {
                    let d = self.discriminant(
                        i,
                        o,
                        k,
                        n,
                        &scrutinee.0,
                        cases.iter().map(|c| (&*c.0, c.1.1.iter().map(|a| &a.0))),
                        &i.blocks[k].orig_span.unwrap_or(Span::dummy_with_cmt()),
                    );
                    let v = o.regs.alloc(());
                    o.decls.insert(v.clone());
                    o.blocks[n].stmts.push(TStmt {
                        left: LId::Id { id: v.clone() },
                        flags: ValFlags::default(),
                        right: d,
                        span: i.blocks[k].orig_span.unwrap_or(Span::dummy_with_cmt()),
                    });
                    TTerm::Switch {
                        x: v,
                        blocks: cases
                            .iter()
                            .enumerate()
                            .map(|(idx, (_, (b, _)))| {
                                let c = self.convert_block(i, o, *b)?;
                                let v = o.regs.alloc(());
                                o.decls.insert(v.clone());
                                o.blocks[n].stmts.push(TStmt {
                                    left: LId::Id { id: v.clone() },
                                    flags: ValFlags::default(),
                                    right: Item::Lit {
                                        lit: Lit::Num(Number {
                                            span: i.blocks[k]
                                                .orig_span
                                                .unwrap_or(Span::dummy_with_cmt()),
                                            value: idx as f64,
                                            raw: None,
                                        }),
                                    },
                                    span: i.blocks[k].orig_span.unwrap_or(Span::dummy_with_cmt()),
                                });
                                Ok((v, c))
                            })
                            .collect::<anyhow::Result<_>>()?,
                        default: n,
                    }
                }
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
                                        value: b.clone().into(),
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
                            value: k.clone().into(),
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
                        value: b.clone().into(),
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
    fn discriminant<'a, 'b>(
        &mut self,
        i: &TSimplCfg<D>,
        o: &mut TCfg,
        k: Id<TSimplBlock<D>>,
        mut n: Id<TBlock>,
        left: &SimplPathId,
        ids: impl Iterator<Item = (&'a crate::Ident, impl Iterator<Item = &'b SimplPathId>)>,
        span: &Span,
    ) -> crate::Item<swc_ecma_ast::Id, TFunc> {
        let v = o.regs.alloc(());
        o.decls.insert(v.clone());
        o.blocks[n].stmts.push(TStmt {
            left: LId::Id { id: v.clone() },
            flags: ValFlags::default(),
            right: Item::Lit {
                lit: Lit::Str(Str {
                    span: *span,
                    value: Wtf8Atom::new("$match"),
                    raw: None,
                }),
            },
            span: *span,
        });
        let member = v;
        let item = Item::Obj {
            members: ids
                .collect::<Vec<_>>()
                .into_iter()
                .enumerate()
                .map(|(idx, (a, b))| {
                    (
                        PropKey::Lit(PropSym {
                            sym: a.0.clone(),
                            span: Span::dummy_with_cmt(),
                            ctx: a.1,
                        }),
                        PropVal::Method({
                            let mut f: TFunc = Default::default();
                            for x in b {
                                let v = f.cfg.regs.alloc(());
                                f.params.push(v.clone());
                                f.cfg.blocks[f.entry].stmts.push(TStmt {
                                    left: self.convert_path_lid(i, o, k, n, x, span),
                                    flags: Default::default(),
                                    right: Item::Just { id: v.clone() },
                                    span: *span,
                                });
                            }
                            let v = o.regs.alloc(());
                            o.decls.insert(v.clone());
                            o.blocks[n].stmts.push(TStmt {
                                left: LId::Id { id: v.clone() },
                                flags: ValFlags::default(),
                                right: Item::Lit {
                                    lit: Lit::Num(Number {
                                        span: *span,
                                        value: idx as f64,
                                        raw: None,
                                    }),
                                },
                                span: *span,
                            });
                            let idx = v;
                            f.cfg.blocks[f.entry].post.term = TTerm::Return(Some(idx));
                            f
                        }),
                    )
                })
                .collect(),
        };
        let v = o.regs.alloc(());
        o.decls.insert(v.clone());
        o.blocks[n].stmts.push(TStmt {
            left: LId::Id { id: v.clone() },
            flags: ValFlags::default(),
            right: item,
            span: *span,
        });
        Item::Call {
            callee: TCallee::Member {
                func: self.convert_path(i, o, k, n, left, span),
                member,
            },
            args: [v]
                .into_iter()
                .map(|a| SpreadOr {
                    value: a,
                    is_spread: false,
                })
                .collect(),
        }
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
        let right: Item<swc_ecma_ast::Id, TFunc> = match right {
            SimplItem::Just { id } => Item::Just { id: path!(&id.0) },
            SimplItem::Bin { left, right, op } => Item::Bin {
                left: path!(&left.0),
                right: path!(&right.0),
                op: *op,
            },
            SimplItem::Lit { lit } => Item::Lit { lit: lit.clone() },
            SimplItem::CallStatic { r#fn, args } => Item::Call {
                callee: TCallee::Val(path!(&r#fn.path.0)),
                args: args
                    .iter()
                    .map(|a| path!(&a.0))
                    .map(|a| SpreadOr {
                        value: a,
                        is_spread: false,
                    })
                    .collect(),
            },
            SimplItem::CallTag { tag, args } => match tag.path {},
            SimplItem::DiscriminantIn { value, ids } => self.discriminant(
                i,
                o,
                k,
                n,
                &value.0,
                ids.iter().map(|(a, b)| (a, b.iter().map(|c| &c.0))),
                span,
            ),
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
