use std::mem::replace;

use crate::*;
impl TFunc {
    pub fn splatted(&self, map: Mapper<'_>) -> TFunc {
        let mut s = Splatting::default();
        let mut new = TCfg::default();
        let ne = s.translate(&self.cfg, &mut new, self.entry, map);
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
    pub stack: BTreeSet<Ident>,
}
impl Splatting {
    pub fn translate(
        &mut self,
        input: &TCfg,
        output: &mut TCfg,
        in_block: Id<TBlock>,
        map: Mapper<'_>,
    ) -> Id<TBlock> {
        let semantic = map.semantic;
        let consts = map.consts.as_deref();
        loop {
            if let Some(b) = self.cache.get(&in_block) {
                return *b;
            }
            let mut out_block = output.blocks.alloc(Default::default());
            self.cache.insert(in_block, out_block);
            for d in input.decls.iter() {
                if output.decls.contains(d) {
                    continue;
                };
                output.decls.insert(d.clone());
            }
            output.blocks[out_block].post.catch = match &input.blocks[in_block].post.catch {
                TCatch::Throw => self.catch.clone(),
                TCatch::Jump { pat, k } => TCatch::Jump {
                    pat: pat.clone(),
                    k: self.translate(input, output, *k, map.bud()),
                },
            };
            'b: for stmt in input.blocks[in_block].stmts.iter() {
                let mut stmt = stmt.clone();
                stmt.right = stmt
                    .right
                    .map2(&mut (), &mut |_, i| Ok::<_, Infallible>(i), &mut |_, f| {
                        Ok(f.splatted(map.bud()))
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
                    macro_rules! func {
                        ($value:expr, $func:expr, $arrow:expr) => {
                            match $func {
                                func => match $arrow {
                                    arrow => {
                                        for (param, arg) in func
                                            .params
                                            .iter()
                                            .cloned()
                                            .map(Some)
                                            .chain(once(None).cycle())
                                            .zip(
                                                args.iter()
                                                    .cloned()
                                                    .map(Some)
                                                    .chain(once(None).cycle()),
                                            )
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
                                            this_val: if arrow || (!func.cfg.has_this()) {
                                                self.this_val.clone()
                                            } else {
                                                Some((Atom::new("globalThis"), Default::default()))
                                            },
                                            stack: self
                                                .stack
                                                .iter()
                                                .cloned()
                                                .chain([$value])
                                                .collect(),
                                        };
                                        let c =
                                            new.translate(&func.cfg, output, func.entry, map.bud());
                                        output.blocks[replace(&mut out_block, d)].post.term =
                                            TTerm::Jmp(c);
                                        continue 'b;
                                    }
                                },
                            }
                        };
                    }
                    let mut value = value.clone();
                    'a: loop {
                        if !self.stack.contains(&value) {
                            if let Some(e) = consts
                                .as_deref()
                                .and_then(|a| a.map.get(&value))
                                .map(|a| Box::as_ref(a))
                            {
                                match e {
                                    Expr::Fn(f) => {
                                        if let Ok(g) = (map.to_cfg)(&f.function).and_then(|a| {
                                            TFunc::try_from_with_mapper(&a, map.bud())
                                        }) {
                                            func!(value, g, false)
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            if let Some(Item::Func { func, arrow }) =
                                output.def(LId::Id { id: value.clone() }).cloned()
                            {
                                func!(value, func, arrow);
                                // }
                            }
                        }
                        let Some(Item::Just { id }) =
                            output.def(LId::Id { id: value.clone() }).cloned()
                        else {
                            break;
                        };
                        value = id;
                    }
                }
                if semantic.flags.contains(SemanticFlags::NO_MONKEYPATCHING) {
                    if let Item::Call {
                        callee: TCallee::Member { func, member },
                        args,
                    } = &stmt.right
                    {
                        if let Some(Item::Lit {
                            lit: Lit::Str(method),
                        }) = input.def(LId::Id { id: member.clone() })
                        {
                            macro_rules! func {
                                ($value:expr, $func:expr, $arrow:expr) => {
                                    match $func {
                                        func => match $arrow {
                                            arrow => {
                                                if method.value.as_str() == "call" {
                                                    let mut args_itet = args
                                                        .iter()
                                                        .cloned()
                                                        .map(Some)
                                                        .chain(once(None).cycle());
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
                                                            output.blocks[out_block].stmts.push(
                                                                TStmt {
                                                                    left: LId::Id { id: param },
                                                                    flags: Default::default(),
                                                                    right: match arg {
                                                                        None => Item::Undef,
                                                                        Some(a) => {
                                                                            Item::Just { id: a }
                                                                        }
                                                                    },
                                                                    span: Span::dummy_with_cmt(),
                                                                },
                                                            );
                                                        }
                                                    }
                                                    // if {
                                                    let mut d =
                                                        output.blocks.alloc(Default::default());
                                                    output.blocks[d].post.catch =
                                                        output.blocks[out_block].post.catch.clone();
                                                    let mut new = Splatting {
                                                        cache: Default::default(),
                                                        catch: output.blocks[out_block]
                                                            .post
                                                            .catch
                                                            .clone(),
                                                        ret: Some((stmt.left, d)),
                                                        this_val: if arrow || (!func.cfg.has_this())
                                                        {
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
                                                        stack: self
                                                            .stack
                                                            .iter()
                                                            .cloned()
                                                            .chain([$value])
                                                            .collect(),
                                                    };
                                                    let c = new.translate(
                                                        &func.cfg,
                                                        output,
                                                        func.entry,
                                                        map.bud(),
                                                    );
                                                    output.blocks[replace(&mut out_block, d)]
                                                        .post
                                                        .term = TTerm::Jmp(c);
                                                    continue 'b;
                                                }
                                            }
                                        },
                                    }
                                };
                            }

                            let mut value = func.clone();
                            'a: loop {
                                if !self.stack.contains(&value) {
                                    if let Some(e) = consts
                                        .as_deref()
                                        .and_then(|a| a.map.get(&value))
                                        .map(|a| Box::as_ref(a))
                                    {
                                        match e {
                                            Expr::Fn(f) => {
                                                if let Ok(g) =
                                                    (map.to_cfg)(&f.function).and_then(|a| {
                                                        TFunc::try_from_with_mapper(&a, map.bud())
                                                    })
                                                {
                                                    func!(value, g, false)
                                                }
                                            }
                                            _ => {}
                                        }
                                    }
                                    if let Some(Item::Func { func, arrow }) =
                                        output.def(LId::Id { id: value.clone() }).cloned()
                                    {
                                        func!(value, func, arrow);
                                        // }
                                    }
                                }
                                let Some(Item::Just { id }) =
                                    output.def(LId::Id { id: value.clone() }).cloned()
                                else {
                                    break;
                                };
                                value = id;
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
                TTerm::Tail { callee, args } => match self.ret.as_ref() {
                    None => TTerm::Tail {
                        callee: callee.clone(),
                        args: args.clone(),
                    },
                    Some((id, b2)) => {
                        output.blocks[out_block].stmts.push(TStmt {
                            left: id.clone(),
                            flags: Default::default(),
                            right: Item::Call {
                                callee: callee.clone(),
                                args: args.clone(),
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
                TTerm::Jmp(id) => TTerm::Jmp(self.translate(input, output, *id, map.bud())),
                TTerm::CondJmp {
                    cond,
                    if_true,
                    if_false,
                } => TTerm::CondJmp {
                    cond: cond.clone(),
                    if_true: self.translate(input, output, *if_true, map.bud()),
                    if_false: self.translate(input, output, *if_false, map.bud()),
                },
                TTerm::Switch { x, blocks, default } => TTerm::Switch {
                    x: x.clone(),
                    blocks: blocks
                        .iter()
                        .map(|(a, k)| (a.clone(), self.translate(input, output, *k, map.bud())))
                        .collect(),
                    default: self.translate(input, output, *default, map.bud()),
                },
                TTerm::Default => TTerm::Default,
            };
        }
    }
}
