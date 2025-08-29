use std::mem::replace;

use crate::*;
impl TFunc {
    pub fn splatted(&self) -> TFunc {
        let mut s = Splatting::default();
        let mut new = TCfg::default();
        let ne = s.translate(&self.cfg, &mut new, self.entry);
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
}
impl Splatting {
    pub fn translate(&mut self, i: &TCfg, o: &mut TCfg, k: Id<TBlock>) -> Id<TBlock> {
        loop {
            if let Some(b) = self.cache.get(&k) {
                return *b;
            }
            let mut b = o.blocks.alloc(Default::default());
            self.cache.insert(k, b);
            o.blocks[b].post.catch = match &i.blocks[k].post.catch {
                TCatch::Throw => self.catch.clone(),
                TCatch::Jump { pat, k } => TCatch::Jump {
                    pat: pat.clone(),
                    k: self.translate(i, o, *k),
                },
            };
            for s in i.blocks[k].stmts.iter() {
                let mut s = s.clone();
                if let Item::Func { func, arrow } = &mut s.right {
                    *func = func.splatted();
                }
                if let Item::Call {
                    callee: TCallee::Val(v),
                    args,
                } = &s.right
                {
                    if let Some(Item::Func { func, arrow }) = i.def(LId::Id { id: v.clone() }) {
                        if *arrow || (!func.cfg.has_this()) {
                            let mut d = o.blocks.alloc(Default::default());
                            o.blocks[d].post.catch = o.blocks[b].post.catch.clone();
                            let mut new = Splatting {
                                cache: Default::default(),
                                catch: o.blocks[b].post.catch.clone(),
                                ret: Some((s.left, d)),
                            };
                            let c = new.translate(&func.cfg, o, func.entry);
                            o.blocks[replace(&mut b, d)].post.term = TTerm::Jmp(c);
                            continue;
                        }
                    }
                }
                o.blocks[b].stmts.push(s);
            }
            o.blocks[b].post.orig_span = i.blocks[k].post.orig_span;
            o.blocks[b].post.term = match &i.blocks[k].post.term {
                TTerm::Return(r) => match self.ret.as_ref() {
                    None => TTerm::Return(r.clone()),
                    Some((id, b2)) => {
                        o.blocks[b].stmts.push(TStmt {
                            left: id.clone(),
                            flags: Default::default(),
                            right: match r {
                                None => Item::Undef,
                                Some(x) => Item::Just { id: x.clone() },
                            },
                            span: i.blocks[k]
                                .post
                                .orig_span
                                .unwrap_or_else(|| Span::dummy_with_cmt()),
                        });
                        TTerm::Jmp(*b2)
                    }
                },
                TTerm::Throw(t) => match o.blocks[b].post.catch.clone() {
                    TCatch::Throw => TTerm::Throw(t.clone()),
                    TCatch::Jump { pat, k: k2 } => {
                        o.blocks[b].stmts.push(TStmt {
                            left: LId::Id { id: pat.clone() },
                            flags: Default::default(),
                            right: Item::Just { id: t.clone() },
                            span: i.blocks[k]
                                .post
                                .orig_span
                                .unwrap_or_else(|| Span::dummy_with_cmt()),
                        });
                        TTerm::Jmp(k2)
                    }
                },
                TTerm::Jmp(id) => TTerm::Jmp(self.translate(i, o, *id)),
                TTerm::CondJmp {
                    cond,
                    if_true,
                    if_false,
                } => TTerm::CondJmp {
                    cond: cond.clone(),
                    if_true: self.translate(i, o, *if_true),
                    if_false: self.translate(i, o, *if_false),
                },
                TTerm::Switch { x, blocks, default } => TTerm::Switch {
                    x: x.clone(),
                    blocks: blocks
                        .iter()
                        .map(|(a, k)| (a.clone(), self.translate(i, o, *k)))
                        .collect(),
                    default: self.translate(i, o, *default),
                },
                TTerm::Default => TTerm::Default,
            };
        }
    }
}
