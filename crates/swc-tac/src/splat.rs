use std::mem::replace;

use crate::*;
impl TFunc {
    pub fn splatted(&self, semantic: &SemanticCfg) -> TFunc {
        let mut s = Splatting::default();
        let mut new = TCfg::default();
        let ne = s.translate(&self.cfg, &mut new, self.entry, semantic);
        TFunc {
            cfg: new,
            entry: ne,
            params: self.params.clone(),
            ts_params: self.ts_params.clone(),
            is_generator: self.is_generator,
            is_async: self.is_async,
        }
    }
}
#[derive(Default)]
pub struct Splatting {
    pub cache: BTreeMap<Id<TBlock>, Id<TBlock>>,
    pub catch: TCatch,
    pub ret: Option<(LId, Id<TBlock>)>,
    pub this_val: Option<Ident>,
}
impl Splatting {
    pub fn translate(
        &mut self,
        input: &TCfg,
        output: &mut TCfg,
        in_block: Id<TBlock>,
        semantic: &SemanticCfg,
    ) -> Id<TBlock> {
        loop {
            if let Some(b) = self.cache.get(&in_block) {
                return *b;
            }
            let mut out_block = output.blocks.alloc(Default::default());
            self.cache.insert(in_block, out_block);
            output.blocks[out_block].post.catch = match &input.blocks[in_block].post.catch {
                TCatch::Throw => self.catch.clone(),
                TCatch::Jump { pat, k } => TCatch::Jump {
                    pat: pat.clone(),
                    k: self.translate(input, output, *k, semantic),
                },
            };
            for stmt in input.blocks[in_block].stmts.iter() {
                let mut stmt = stmt.clone();
                stmt.right = stmt
                    .right
                    .map2(&mut (), &mut |_, i| Ok::<_, Infallible>(i), &mut |_, f| {
                        Ok(f.splatted(semantic))
                    })
                    .unwrap();
                if let Some(thid) = self.this_val.as_ref() {
                    if let Item::This = &mut stmt.right {
                        stmt.right = Item::Just { id: thid.clone() }
                    }
                }
                if let Item::Call {
                    callee: TCallee::Val(value),
                    args,
                } = &stmt.right
                {
                    if let Some(Item::Func { func, arrow }) =
                        input.def(LId::Id { id: value.clone() })
                    {
                        for (param, arg) in func
                            .params
                            .iter()
                            .cloned()
                            .map(Some)
                            .chain(once(None).cycle())
                            .zip(args.iter().cloned().map(Some).chain(once(None).cycle()))
                        {
                            if param.is_none() && arg.is_none() {
                                break;
                            }
                            if let Some(param) = param {
                                output.blocks[out_block].stmts.push(TStmt {
                                    left: LId::Id { id: param },
                                    flags: Default::default(),
                                    right: match arg {
                                        None => Item::Undef,
                                        Some(a) => Item::Just { id: a },
                                    },
                                    span: Span::dummy_with_cmt(),
                                });
                            }
                        }
                        // if {
                        let mut d = output.blocks.alloc(Default::default());
                        output.blocks[d].post.catch = output.blocks[out_block].post.catch.clone();
                        let mut new = Splatting {
                            cache: Default::default(),
                            catch: output.blocks[out_block].post.catch.clone(),
                            ret: Some((stmt.left, d)),
                            this_val: if *arrow || (!func.cfg.has_this()) {
                                self.this_val.clone()
                            } else {
                                Some((Atom::new("globalThis"), Default::default()))
                            },
                        };
                        let c = new.translate(&func.cfg, output, func.entry, semantic);
                        output.blocks[replace(&mut out_block, d)].post.term = TTerm::Jmp(c);
                        continue;
                        // }
                    }
                }
                if semantic.flags.contains(SemanticFlags::ASSUME_SES) {
                    if let Item::Call {
                        callee: TCallee::Member { func, member },
                        args,
                    } = &stmt.right
                    {
                        if let Some(Item::Lit {
                            lit: Lit::Str(method),
                        }) = input.def(LId::Id { id: member.clone() })
                        {
                            if let Some(Item::Func { func, arrow }) =
                                input.def(LId::Id { id: func.clone() })
                            {
                                if method.value.as_str() == "call" {
                                    let mut args_itet =
                                        args.iter().cloned().map(Some).chain(once(None).cycle());
                                    let this_arg = args_itet.next().unwrap();
                                    for (param, arg) in func
                                        .params
                                        .iter()
                                        .cloned()
                                        .map(Some)
                                        .chain(once(None).cycle())
                                        .zip(args_itet)
                                    {
                                        if param.is_none() && arg.is_none() {
                                            break;
                                        }
                                        if let Some(param) = param {
                                            output.blocks[out_block].stmts.push(TStmt {
                                                left: LId::Id { id: param },
                                                flags: Default::default(),
                                                right: match arg {
                                                    None => Item::Undef,
                                                    Some(a) => Item::Just { id: a },
                                                },
                                                span: Span::dummy_with_cmt(),
                                            });
                                        }
                                    }
                                    // if {
                                    let mut d = output.blocks.alloc(Default::default());
                                    output.blocks[d].post.catch =
                                        output.blocks[out_block].post.catch.clone();
                                    let mut new = Splatting {
                                        cache: Default::default(),
                                        catch: output.blocks[out_block].post.catch.clone(),
                                        ret: Some((stmt.left, d)),
                                        this_val: if *arrow || (!func.cfg.has_this()) {
                                            self.this_val.clone()
                                        } else {
                                            match this_arg {
                                                None => Some((
                                                    Atom::new("globalThis"),
                                                    Default::default(),
                                                )),
                                                Some(arg) => Some(arg),
                                            }
                                        },
                                    };
                                    let c = new.translate(&func.cfg, output, func.entry, semantic);
                                    output.blocks[replace(&mut out_block, d)].post.term =
                                        TTerm::Jmp(c);
                                    continue;
                                }
                                // }
                            }
                        }
                    }
                }
                output.blocks[out_block].stmts.push(stmt);
            }
            output.blocks[out_block].post.orig_span = input.blocks[in_block].post.orig_span;
            output.blocks[out_block].post.term = match &input.blocks[in_block].post.term {
                TTerm::Return(r) => match self.ret.as_ref() {
                    None => TTerm::Return(r.clone()),
                    Some((id, b2)) => {
                        output.blocks[out_block].stmts.push(TStmt {
                            left: id.clone(),
                            flags: Default::default(),
                            right: match r {
                                None => Item::Undef,
                                Some(x) => Item::Just { id: x.clone() },
                            },
                            span: input.blocks[in_block]
                                .post
                                .orig_span
                                .unwrap_or_else(|| Span::dummy_with_cmt()),
                        });
                        TTerm::Jmp(*b2)
                    }
                },
                TTerm::Throw(t) => match output.blocks[out_block].post.catch.clone() {
                    TCatch::Throw => TTerm::Throw(t.clone()),
                    TCatch::Jump { pat, k: k2 } => {
                        output.blocks[out_block].stmts.push(TStmt {
                            left: LId::Id { id: pat.clone() },
                            flags: Default::default(),
                            right: Item::Just { id: t.clone() },
                            span: input.blocks[in_block]
                                .post
                                .orig_span
                                .unwrap_or_else(|| Span::dummy_with_cmt()),
                        });
                        TTerm::Jmp(k2)
                    }
                },
                TTerm::Jmp(id) => TTerm::Jmp(self.translate(input, output, *id, semantic)),
                TTerm::CondJmp {
                    cond,
                    if_true,
                    if_false,
                } => TTerm::CondJmp {
                    cond: cond.clone(),
                    if_true: self.translate(input, output, *if_true, semantic),
                    if_false: self.translate(input, output, *if_false, semantic),
                },
                TTerm::Switch { x, blocks, default } => TTerm::Switch {
                    x: x.clone(),
                    blocks: blocks
                        .iter()
                        .map(|(a, k)| (a.clone(), self.translate(input, output, *k, semantic)))
                        .collect(),
                    default: self.translate(input, output, *default, semantic),
                },
                TTerm::Default => TTerm::Default,
            };
        }
    }
}
