use crate::*;

pub trait ItemFetcher {
    type Function;
    fn fetch<'a>(&'a self) -> Option<Item<PropKey<&'a Self>, &'a Self::Function>>;
}
impl ItemFetcher for Expr {
    type Function = Function;

    fn fetch<'a>(&'a self) -> Option<Item<PropKey<&'a Self>, &'a Self::Function>> {
        let p = |a: &'a Self| PropKey::Computed(a);
        match self {
            Expr::Lit(l) => Some(Item::Lit { lit: l.clone() }),
            Expr::Unary(u) => Some(Item::Un {
                arg: p(&u.arg),
                op: u.op,
            }),
            Expr::Bin(b) => Some(Item::Bin {
                left: p(&b.left),
                right: p(&b.right),
                op: b.op,
            }),
            Expr::Fn(f) => Some(Item::Func {
                func: &f.function,
                arrow: false,
            }),
            Expr::Call(c) => Some(Item::Call {
                callee: match &c.callee {
                    Callee::Super(_) => TCallee::Super,
                    Callee::Import(import) => TCallee::Import,
                    Callee::Expr(expr) => match &**expr {
                        Expr::Ident(i) if !i.optional && i.sym == "eval" => TCallee::Eval,
                        Expr::Member(m) => match &m.prop {
                            MemberProp::Ident(ident_name) => TCallee::Member {
                                func: p(&m.obj),
                                member: PropKey::Lit((ident_name.sym.clone(), Default::default())),
                            },
                            MemberProp::PrivateName(private_name) => TCallee::PrivateMember {
                                func: p(&m.obj),
                                member: Private {
                                    sym: private_name.name.clone(),
                                    ctxt: Default::default(),
                                    span: private_name.span,
                                },
                            },
                            MemberProp::Computed(computed_prop_name) => TCallee::Member {
                                func: p(&m.obj),
                                member: p(&computed_prop_name.expr),
                            },
                        },
                        e => TCallee::Val(p(e)),
                    },
                },
                args: c
                    .args
                    .iter()
                    .map(|a| SpreadOr {
                        value: p(&*a.expr),
                        is_spread: a.spread.is_some(),
                    })
                    .collect(),
            }),
            Expr::Member(m) => Some(match &m.prop {
                MemberProp::Ident(ident_name) => Item::Mem {
                    obj: p(&m.obj),
                    mem: PropKey::Lit((ident_name.sym.clone(), Default::default())),
                },
                MemberProp::PrivateName(private_name) => Item::PrivateMem {
                    obj: p(&m.obj),
                    mem: Private {
                        sym: private_name.name.clone(),
                        ctxt: Default::default(),
                        span: private_name.span,
                    },
                },
                MemberProp::Computed(computed_prop_name) => Item::Mem {
                    obj: p(&m.obj),
                    mem: p(&computed_prop_name.expr),
                },
            }),
            _ => None,
        }
    }
}
