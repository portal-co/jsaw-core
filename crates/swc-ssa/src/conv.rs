use ssa_impls::dom::dominates;

use crate::*;

#[non_exhaustive]
pub struct ToSSAConverter {
    pub map: BTreeMap<Id<TBlock>, Id<SBlock>>,
    pub all: BTreeSet<Ident>,
    pub undef: Id<SValueW>,
    pub domtree: BTreeMap<Option<Id<TBlock>>, Id<TBlock>>,
}
impl ToSSAConverter {
    fn safe_to_carry(&self, target: Id<TBlock>, src: Id<TBlock>) -> bool {
        dominates::<TFunc>(&self.domtree, Some(src), Some(target))
    }
    // pub fn from_undef(undef: Id<SValueW>) -> Self {
    //     Self {
    //         map: Default::default(),
    //         all: Default::default(),
    //         undef: undef,
    //     }
    // }
    pub fn apply_shim(
        &self,
        o: &mut SCfg,
        state: &BTreeMap<Ident, (Id<SValueW>, ValFlags)>,
        s: &Option<(Id<SBlock>, Vec<Ident>)>,
        x: Id<SBlock>,
    ) {
        let Some((a, b)) = s else {
            o.blocks[x].postcedent.catch = SCatch::Throw;
            return;
        };
        let k = SCatch::Just {
            target: STarget {
                block: *a,
                args: b
                    .iter()
                    .filter_map(|x| state.get(x))
                    .map(|a| &a.0)
                    .cloned()
                    .collect(),
            },
        };
        o.blocks[x].postcedent.catch = k;
    }
    pub fn load(
        &self,
        state: &BTreeMap<Ident, (Id<SValueW>, ValFlags)>,
        i: &TCfg,
        o: &mut SCfg,
        t: Id<SBlock>,
        a: Ident,
        cache: &BTreeMap<Ident, Id<SValueW>>,
    ) -> anyhow::Result<Id<SValueW>> {
        if let Some(k) = cache.get(&a) {
            return Ok(*k);
        }
        if let Some(d) = i.def(LId::Id { id: a.clone() }) {
            if inlinable(d, i) {
                let b = 'a: {
                    let b = match d {
                        Item::Undef => break 'a self.undef,
                        b => b.clone().map2::<_, _, anyhow::Error, ()>(
                            &mut (),
                            &mut |_, a| self.load(&state, i, o, t, a.clone(), &cache),
                            &mut |_, b| b.try_into(),
                        )?,
                    };
                    o.values.alloc(
                        SValue::Item {
                            item: b,
                            span: None,
                        }
                        .into(),
                    )
                };
                o.blocks[t].stmts.push(b);
                return Ok(b);
            }
        }
        let x = match state.get(&a).cloned() {
            Some(b) => b.0,
            None => {
                let v = o.values.alloc(SValue::LoadId(a).into());
                o.blocks[t].stmts.push(v);
                return Ok(v);
            }
        };
        if let Some(ty) = i.type_annotations.get(&a).cloned() {
            o.ts.insert(x, ty);
        };
        Ok(x)
    }
    pub fn trans(
        &mut self,
        i: &TCfg,
        o: &mut SCfg,
        k: Id<TBlock>,
        app: &mut (dyn Iterator<Item = (Ident, Id<SValueW>)> + '_),
    ) -> anyhow::Result<Id<SBlock>> {
        self.convert_block(i, o, k, app)
    }

    // Private helper for block/term conversion
    fn convert_block(
        &mut self,
        i: &TCfg,
        o: &mut SCfg,
        k: Id<TBlock>,
        app: &mut (dyn Iterator<Item = (Ident, Id<SValueW>)> + '_),
    ) -> anyhow::Result<Id<SBlock>> {
        loop {
            if let Some(a) = self.map.get(&k) {
                return Ok(*a);
            }
            let mut t = o.blocks.alloc(SBlock {
                params: vec![],
                stmts: vec![],
                postcedent: SPostcedent::default(),
            });
            self.map.insert(k, t);
            let app: BTreeMap<_, _> = app.collect();
            let ok = k;
            let shim: Option<(Id<SBlock>, Vec<Ident>)> = match &i.blocks[k].post.catch {
                swc_tac::TCatch::Throw => None,
                swc_tac::TCatch::Jump { pat, k: b } => {
                    let a = o.blocks.alloc(SBlock {
                        params: vec![],
                        stmts: vec![],
                        postcedent: SPostcedent::default(),
                    });
                    let b = *b;
                    // let d = self.domtree.get(&Some(*k)).cloned() == Some(Some(ok));
                    let d = self.safe_to_carry(b, k);
                    let state2 = once(pat.clone())
                        .chain(
                            self.all
                                .iter()
                                .filter(|a| {
                                    !d || i.blocks.iter().all(|k| {
                                        k.1.stmts.iter().all(|i| {
                                            !i.will_store(a)
                                                || !i.flags.contains(ValFlags::SSA_LIKE)
                                        })
                                    })
                                })
                                .filter(|a| *a != pat)
                                .cloned(),
                        )
                        .collect::<Vec<_>>();
                    let v = state2
                        .iter()
                        .cloned()
                        .map(|a2| (a2, o.add_blockparam(a)))
                        .collect::<BTreeMap<_, _>>();
                    let p = self
                        .all
                        .iter()
                        .filter_map(|x| v.get(x))
                        .cloned()
                        .collect::<Vec<_>>();
                    let t = STerm::Jmp(STarget {
                        block: self.trans(
                            i,
                            o,
                            b,
                            &mut app.iter().map(|(k, v)| (k.clone(), v.clone())),
                        )?,
                        args: p,
                    });
                    o.blocks[a].postcedent.term = t;
                    Some((a, state2))
                }
            };
            let mut state = self
                .all
                .iter()
                .filter(|a| !app.contains_key(&**a))
                .map(|a| (a.clone(), (o.add_blockparam(t), ValFlags::all())))
                .chain(
                    app.iter()
                        .map(|(a, b)| (a.clone(), b.clone()))
                        .map(|(a, b)| (a, (b, ValFlags::all()))),
                )
                .collect::<BTreeMap<_, _>>();
            self.apply_shim(o, &state, &shim, t);
            let mut cache = BTreeMap::new();
            for TStmt {
                left: a,
                flags,
                right: b,
                span: s,
            } in i.blocks[k].stmts.iter()
            {
                let nothrow = b.nothrow();
                let b = b.as_ref();
                let b = 'a: {
                    let b = match b {
                        Item::Undef => break 'a self.undef,
                        b => b.map2::<_, _, anyhow::Error, ()>(
                            &mut (),
                            &mut |_, a| self.load(&state, i, o, t, a.clone(), &cache),
                            &mut |_, b| b.try_into(),
                        )?,
                    };
                    o.values.alloc(
                        SValue::Item {
                            item: b,
                            span: Some(*s),
                        }
                        .into(),
                    )
                };
                o.blocks[t].stmts.push(b);
                match a.clone() {
                    LId::Id { id } => match state.get_mut(&id) {
                        Some((a, f)) => {
                            *f &= *flags;
                            let f = *f;
                            *a = b;
                            if !f.contains(ValFlags::SSA_LIKE) && shim.is_some() && !nothrow {
                                let u = o.blocks.alloc(SBlock {
                                    params: vec![],
                                    stmts: vec![],
                                    postcedent: Default::default(),
                                });
                                self.apply_shim(o, &state, &shim, u);
                                o.blocks[t].postcedent.term = STerm::Jmp(STarget {
                                    block: u,
                                    args: vec![],
                                });
                                t = u;
                            }
                        }
                        None => {
                            if flags.contains(ValFlags::SSA_LIKE) {
                                state.insert(id.clone(), (b, *flags));
                            } else {
                                cache.insert(id.clone(), b);
                                let c = o.values.alloc(
                                    SValue::StoreId {
                                        target: id.clone(),
                                        val: b,
                                    }
                                    .into(),
                                );
                                o.blocks[t].stmts.push(c);
                            }
                        }
                    },
                    a => {
                        let c = a.map::<_, anyhow::Error>(&mut |a| {
                            self.load(&state, i, o, t, a, &cache)
                        })?;
                        let c = o.values.alloc(SValue::Assign { target: c, val: b }.into());
                        o.blocks[t].stmts.push(c);
                    }
                }
            }
            let params = |this: &Self, k2: Id<TBlock>| {
                let d = this.safe_to_carry(k2, k);
                this.all
                    .iter()
                    .filter(|a| {
                        !d || i.blocks.iter().all(|k| {
                            k.1.stmts.iter().all(|i| {
                                i.left != LId::Id { id: (**a).clone() }
                                    || !i.flags.contains(ValFlags::SSA_LIKE)
                            })
                        })
                    })
                    .filter_map(|a| state.get(a))
                    .map(|a| &a.0)
                    .cloned()
                    .collect::<Vec<_>>()
            };
            let dtc = |this: &Self, k2: Id<TBlock>| {
                let d = this.safe_to_carry(k2, k);
                if d {
                    app.clone()
                        .into_iter()
                        .chain(
                            this.all
                                .iter()
                                .filter(|a| {
                                    !i.blocks.iter().all(|k| {
                                        k.1.stmts.iter().all(|i| {
                                            i.left != LId::Id { id: (**a).clone() }
                                                || !i.flags.contains(ValFlags::SSA_LIKE)
                                        })
                                    })
                                })
                                .filter_map(|a| state.get(a).map(|b| (a.clone(), b.0))),
                        )
                        .collect::<BTreeMap<_, _>>()
                } else {
                    app.clone()
                }
            };
            let term = i.blocks[k].post.term.as_ref().map(
                &mut (&mut *self, &mut *o),
                &mut |(this, o), id| {
                    let id2 = this.trans(i, o, *id, &mut dtc(this, *id).into_iter())?;
                    Ok(STarget {
                        block: id2,
                        args: params(this, *id),
                    })
                },
                &mut |(this, o), a| this.load(&state, i, o, t, a.clone(), &cache),
            )?;
            // let term = match &i.blocks[k].post.term {
            //     TTerm::Tail { callee, args } => TTerm::Tail {
            //         callee: callee
            //             .as_ref()
            //             .map(&mut |a| self.load(&state, i, o, t, a.clone(), &cache))?,
            //         args: args
            //             .iter()
            //             .map(|a| self.load(&state, i, o, t, a.clone(), &cache))
            //             .collect::<Result<_, _>>()?,
            //     },
            //     swc_tac::TTerm::Return(ident) => match ident.as_ref() {
            //         None => STerm::Return(None),
            //         Some(a) => {
            //             STerm::Return(Some(self.load(&state, i, o, t, a.clone(), &cache)?))
            //         }
            //     },
            //     swc_tac::TTerm::Throw(ident) => {
            //         STerm::Throw(self.load(&state, i, o, t, ident.clone(), &cache)?)
            //     }
            //     swc_tac::TTerm::Jmp(id) => {
            //         let id2 = self.trans(i, o, *id, &mut dtc(self, *id).into_iter())?;
            //         STerm::Jmp(STarget {
            //             block: id2,
            //             args: params(self, *id),
            //         })
            //     }
            //     swc_tac::TTerm::CondJmp {
            //         cond,
            //         if_true,
            //         if_false,
            //     } => {
            //         let if_true2 =
            //             self.trans(i, o, *if_true, &mut dtc(self, *if_true).into_iter())?;
            //         let if_true = STarget {
            //             block: if_true2,
            //             args: params(self, *if_true),
            //         };
            //         let if_false2 =
            //             self.trans(i, o, *if_false, &mut dtc(self, *if_false).into_iter())?;
            //         let if_false = STarget {
            //             block: if_false2,
            //             args: params(self, *if_false),
            //         };
            //         let cond = self.load(&state, i, o, t, cond.clone(), &cache)?;
            //         STerm::CondJmp {
            //             cond,
            //             if_true,
            //             if_false,
            //         }
            //     }
            //     swc_tac::TTerm::Switch { x, blocks, default } => {
            //         let x = self.load(&state, i, o, t, x.clone(), &cache)?;
            //         let blocks = blocks
            //             .iter()
            //             .map(|(a, b)| {
            //                 let c = self.trans(i, o, *b, &mut dtc(self, *b).into_iter())?;
            //                 let d = self.load(&state, i, o, t, a.clone(), &cache)?;
            //                 Ok((
            //                     d,
            //                     STarget {
            //                         block: c,
            //                         args: params(self, *b),
            //                     },
            //                 ))
            //             })
            //             .collect::<anyhow::Result<Vec<_>>>()?;
            //         let default2 =
            //             self.trans(i, o, *default, &mut dtc(self, *default).into_iter())?;
            //         let default = STarget {
            //             block: default2,
            //             args: params(self, *default),
            //         };
            //         STerm::Switch { x, blocks, default }
            //     }
            //     swc_tac::TTerm::Default => STerm::Default,
            // };
            o.blocks[t].postcedent.term = term;
        }
    }
}
impl<'a> TryFrom<&'a TFunc> for SFunc {
    type Error = anyhow::Error;

    fn try_from(value: &'a TFunc) -> Result<Self, Self::Error> {
        let domtree = ssa_impls::dom::domtree(value)
            .into_iter()
            // .map(|(a, b)| (a, Some(b)))
            .collect::<BTreeMap<_, _>>();
        let mut decls = value.cfg.decls.clone();
        let mut d = BTreeSet::new();
        for e in value.cfg.externs().collect::<BTreeSet<_>>() {
            decls.remove(&e);
            d.insert(e);
        }
        let mut cfg = SCfg {
            blocks: Default::default(),
            values: Default::default(),
            ts: Default::default(),
            decls: d,
            generics: None,
            ts_retty: None,
        };
        let entry2 = cfg.blocks.alloc(Default::default());
        let params = value
            .params
            .iter()
            .cloned()
            .map(|a| (a, cfg.add_blockparam(entry2)))
            .collect::<BTreeMap<_, _>>();
        let undef = cfg.values.alloc(
            SValue::Item {
                item: Item::Undef,
                span: None,
            }
            .into(),
        );
        cfg.blocks[entry2].stmts.push(undef);
        let mut trans = ToSSAConverter {
            map: BTreeMap::new(),
            all: decls.clone(),
            undef,
            domtree,
        };
        let entry = trans.trans(&value.cfg, &mut cfg, value.entry, &mut empty())?;
        let target = STarget {
            block: entry,
            args: decls
                .iter()
                .cloned()
                .map(|a| match params.get(&a) {
                    Some(v) => *v,
                    None => undef,
                })
                .collect(),
        };
        cfg.blocks[entry2].postcedent.term = STerm::Jmp(target);
        cfg.generics = value.cfg.generics.clone();
        cfg.ts_retty = value.cfg.ts_retty.clone();
        Ok(Self {
            cfg,
            entry: entry2,
            is_generator: value.is_generator,
            is_async: value.is_async,
            ts_params: value.ts_params.clone(),
        })
    }
}
