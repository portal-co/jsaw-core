use std::collections::{BTreeMap, HashMap};
use std::convert::Infallible;

use anyhow::Context;
use id_arena::Id;
use swc_atoms::Atom;
use swc_cfg::{Block, Cfg};
use swc_cfg::{Func, Term};
use swc_common::{Span, Spanned, SyntaxContext};
use swc_ecma_ast::{ArrayLit, CondExpr, NewExpr, Param, PrivateMethod, PrivateName};
use swc_ecma_ast::{ArrowExpr, KeyValueProp};
use swc_ecma_ast::{AssignExpr, Decl, SeqExpr, VarDecl, VarDeclarator};
use swc_ecma_ast::{AssignOp, ExprOrSpread};
use swc_ecma_ast::{AssignTarget, Function};
use swc_ecma_ast::{BinExpr, BindingIdent, TsTypeAnn};
use swc_ecma_ast::{BinaryOp, CallExpr, Lit, Number};
use swc_ecma_ast::{BlockStmt, FnExpr, GetterProp, ReturnStmt};
use swc_ecma_ast::{Callee, MemberExpr};
use swc_ecma_ast::{Class, ClassExpr, Pat};
use swc_ecma_ast::{ClassMember, ClassMethod, ClassProp, Prop};
use swc_ecma_ast::{ComputedPropName, ThisExpr};
use swc_ecma_ast::{Constructor, ParamOrTsParamProp, PropOrSpread};
use swc_ecma_ast::{Expr, SimpleAssignTarget};
use swc_ecma_ast::{ExprStmt, Str};
use swc_ecma_ast::{Id as Ident, SetterProp};
use swc_ecma_ast::{IdentName, Stmt};
use swc_ecma_ast::{MethodProp, ObjectLit};
use swc_ecma_ast::{PrivateProp, UnaryExpr};

use crate::{Item, LId, MemberFlags, PropKey, TBlock, TCallee, TCfg, TFunc};

impl<'a> TryFrom<&'a TFunc> for Func {
    type Error = anyhow::Error;

    fn try_from(value: &'a TFunc) -> Result<Self, Self::Error> {
        let mut cfg = Cfg::default();
        let entry = Rew {
            all: BTreeMap::new(),
        }
        .trans(&mut cfg, &value.cfg, value.entry)?;
        let span = Span::dummy_with_cmt();
        let params = value
            .params
            .iter()
            .zip(value.ts_params.iter())
            .map(|(a, t)| Param {
                span: span,
                decorators: vec![],
                pat: Pat::Ident(BindingIdent {
                    id: ident(a, span),
                    type_ann: t.as_ref().map(|a| {
                        Box::new(TsTypeAnn {
                            span: span,
                            type_ann: Box::new(a.clone()),
                        })
                    }),
                }),
            })
            .collect::<Vec<_>>();
        let entry2 = cfg.blocks.alloc(Default::default());
        for d in value.cfg.decls.iter() {
            cfg.blocks[entry2]
                .stmts
                .push(Stmt::Decl(Decl::Var(Box::new(VarDecl {
                    span: span,
                    ctxt: d.1.clone(),
                    declare: false,
                    kind: swc_ecma_ast::VarDeclKind::Var,
                    decls: vec![VarDeclarator {
                        span: span,
                        name: Pat::Ident(BindingIdent {
                            id: ident(d, span),
                            type_ann: value.cfg.type_annotations.get(d).map(|a| {
                                Box::new(TsTypeAnn {
                                    span: span,
                                    type_ann: Box::new(a.clone()),
                                })
                            }),
                        }),
                        init: None,
                        definite: false,
                    }],
                }))));
        }
        cfg.blocks[entry2].end.term = Term::Jmp(entry);
        cfg.ts_retty = value.cfg.ts_retty.clone();
        cfg.generics = value.cfg.generics.clone();
        Ok(Func {
            cfg,
            entry: entry2,
            params,
            is_generator: value.is_generator,
            is_async: value.is_async,
        })
    }
}
impl TryFrom<TFunc> for Func {
    type Error = anyhow::Error;

    fn try_from(value: TFunc) -> Result<Self, Self::Error> {
        TryFrom::try_from(&value)
    }
}
impl<'a> TryFrom<&'a TFunc> for Function {
    type Error = anyhow::Error;

    fn try_from(value: &'a TFunc) -> Result<Self, Self::Error> {
        let a: Func = value.try_into()?;
        return Ok(a.into());
    }
}
impl TryFrom<TFunc> for Function {
    type Error = anyhow::Error;

    fn try_from(value: TFunc) -> Result<Self, Self::Error> {
        TryFrom::try_from(&value)
    }
}
#[derive(Default)]
#[non_exhaustive]
pub struct Rew {
    pub all: BTreeMap<Id<TBlock>, Id<Block>>,
}
impl Rew {
    pub fn trans(
        &mut self,
        cfg: &mut Cfg,
        tcfg: &TCfg,
        block_id: Id<TBlock>,
    ) -> anyhow::Result<Id<Block>> {
        loop {
            if let Some(existing_block_id) = self.all.get(&block_id) {
                return Ok(*existing_block_id);
            }
            let new_block_id = cfg.blocks.alloc(Default::default());
            cfg.blocks[new_block_id].end.orig_span = tcfg.blocks[block_id].post.orig_span.clone();
            self.all.insert(block_id, new_block_id);
            let catch = match &tcfg.blocks[block_id].post.catch {
                crate::TCatch::Throw => swc_cfg::Catch::Throw,
                crate::TCatch::Jump { pat, k } => swc_cfg::Catch::Jump {
                    pat: Pat::Ident(swc_ecma_ast::BindingIdent {
                        id: ident(pat, Span::dummy_with_cmt()),
                        type_ann: None,
                    }),
                    k: self.trans(cfg, tcfg, *k)?,
                },
            };
            cfg.blocks[new_block_id].end.catch = catch;
            let mut state: HashMap<Ident, Box<Expr>> = HashMap::new();
            let mut ids = vec![];
            macro_rules! flush {
                () => {
                    let s: Vec<_> = ids
                        .drain(..)
                        .filter_map(|a| state.remove(&a).map(|b| (a, b)))
                        .map(|(s, right)| {
                            Box::new(Expr::Assign(AssignExpr {
                                span: right.span(),
                                op: swc_ecma_ast::AssignOp::Assign,
                                left: AssignTarget::Simple(SimpleAssignTarget::Ident(
                                    BindingIdent {
                                        id: ident(&s, right.span()),
                                        type_ann: None,
                                    },
                                )),
                                right,
                            }))
                        })
                        .collect();
                    if s.len() != 0 {
                        // for (s, right) in {
                        cfg.blocks[new_block_id].stmts.push(Stmt::Expr(ExprStmt {
                            span: Span::dummy_with_cmt(),
                            expr: Box::new(Expr::Seq(SeqExpr {
                                span: Span::dummy_with_cmt(),
                                exprs: s,
                            })),
                        }));
                    }
                    // }
                };
            }
            for statement_data in tcfg.blocks[block_id].stmts.iter() {
                let span = statement_data.span;
                let mut mark = false;
                fn _sr(
                    left: &Ident,
                    tcfg: &TCfg,
                    state: &mut HashMap<Ident, Box<Expr>>,
                    span: Span,
                ) -> Box<Expr> {
                    let n = tcfg.refs().filter(|a| a == left).count();
                    match tcfg.def(crate::LId::Id { id: left.clone() }) {
                        Some(Item::Asm { value }) => match value {
                            portal_jsc_common::Asm::OrZero(a) => Box::new(Expr::Bin(BinExpr {
                                span,
                                op: BinaryOp::BitOr,
                                left: _sr(a, tcfg, state, span),
                                right: Box::new(Expr::Lit(Lit::Num(Number {
                                    span,
                                    value: 0.0,
                                    raw: None,
                                }))),
                            })),
                            _ => todo!(),
                        },
                        Some(Item::Lit { lit }) => Box::new(Expr::Lit(lit.clone())),
                        _ => match state.remove(left) {
                            None => Box::new(Expr::Ident(ident(left, span))),
                            Some(right) => match n {
                                0 | 1 => right,
                                _ => Box::new(Expr::Assign(AssignExpr {
                                    span: right.span(),
                                    op: AssignOp::Assign,
                                    left: AssignTarget::Simple(SimpleAssignTarget::Ident(
                                        BindingIdent {
                                            id: ident(left, span),
                                            type_ann: None,
                                        },
                                    )),
                                    right,
                                })),
                            },
                        },
                    }
                }
                let mut sr = |left: &Ident| _sr(left, tcfg, &mut state, span);
                let left = match &statement_data.left {
                    crate::LId::Id { id } => swc_ecma_ast::AssignTarget::Simple(
                        swc_ecma_ast::SimpleAssignTarget::Ident(swc_ecma_ast::BindingIdent {
                            id: ident(id, span),
                            type_ann: None,
                        }),
                    ),
                    crate::LId::Member { obj, mem } => {
                        mark = true;
                        // let obj = ident(obj, span);
                        // let mem = ident(&mem[0], span);
                        AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Member(MemberExpr {
                            span: span,
                            obj: sr(obj),
                            prop: swc_ecma_ast::MemberProp::Computed(
                                swc_ecma_ast::ComputedPropName {
                                    span: span,
                                    expr: sr(&mem[0]),
                                },
                            ),
                        }))
                    }
                    LId::Private { obj, id } => {
                        AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Member(MemberExpr {
                            span: span,
                            obj: sr(obj),
                            prop: swc_ecma_ast::MemberProp::PrivateName(PrivateName {
                                span: id.span,
                                name: id.sym.clone(),
                            }),
                        }))
                    }
                    _ => todo!(),
                };

                let right = Box::new(match &statement_data.right {
                    Item::Select {
                        cond,
                        then,
                        otherwise,
                    } => match 'a: {
                        Box::new(Expr::Seq(SeqExpr {
                            span,
                            exprs: match [cond, then, otherwise]
                                .map(|a| match tcfg.def(LId::Id { id: a.clone() }) {
                                    Some(Item::Lit { .. }) => None,
                                    _ => {
                                        let s = sr(a);
                                        let n = tcfg.refs().filter(|left| a == left).count();
                                        Some(match n {
                                            0 | 1 => Box::new(Expr::Assign(AssignExpr {
                                                span,
                                                op: AssignOp::Assign,
                                                left: AssignTarget::Simple(
                                                    SimpleAssignTarget::Ident(
                                                        ident(a, span).into(),
                                                    ),
                                                ),
                                                right: s,
                                            })),
                                            _ => s,
                                        })
                                    }
                                })
                                .into_iter()
                                .flatten()
                                .chain([sr(cond)])
                                .collect::<Vec<_>>()
                            {
                                mut v => {
                                    if v.len() == 1 {
                                        break 'a v.pop().unwrap();
                                    }
                                    v
                                }
                            },
                        }))
                    } {
                        seq => Expr::Cond(CondExpr {
                            span,
                            test: seq,
                            cons: sr(then),
                            alt: sr(otherwise),
                        }),
                    },
                    crate::Item::Just { id } => Expr::Ident(ident(id, span)),
                    crate::Item::Bin { left, right, op } => Expr::Bin(BinExpr {
                        span: span,
                        op: *op,
                        left: sr(left),
                        right: sr(right),
                    }),
                    Item::HasPrivateMem { obj, mem } => Expr::Bin(BinExpr {
                        span,
                        op: BinaryOp::In,
                        left: Box::new(Expr::PrivateName(PrivateName {
                            span: mem.span,
                            name: mem.sym.clone(),
                        })),
                        right: sr(obj),
                    }),
                    crate::Item::Un { arg, op } => Expr::Unary(UnaryExpr {
                        span: span,
                        op: *op,
                        arg: sr(arg),
                    }),
                    crate::Item::Mem { obj, mem } => {
                        // let obj = ident(obj, span);
                        // let mem = ident(mem, span);
                        mark = true;
                        Expr::Member(MemberExpr {
                            span: span,
                            obj: sr(obj),
                            prop: swc_ecma_ast::MemberProp::Computed(
                                swc_ecma_ast::ComputedPropName {
                                    span: span,
                                    expr: sr(mem),
                                },
                            ),
                        })
                    }
                    Item::PrivateMem { obj, mem } => Expr::Member(MemberExpr {
                        span: span,
                        obj: sr(obj),
                        prop: swc_ecma_ast::MemberProp::PrivateName(PrivateName {
                            span: mem.span,
                            name: mem.sym.clone(),
                        }),
                    }),
                    crate::Item::Func { func, arrow } => match func.try_into()? {
                        func => {
                            if !*arrow {
                                Expr::Fn(FnExpr {
                                    ident: None,
                                    function: Box::new(func),
                                })
                            } else {
                                Expr::Arrow(ArrowExpr {
                                    span: func.span,
                                    ctxt: func.ctxt,
                                    params: func.params.into_iter().map(|a| a.pat).collect(),
                                    body: Box::new(swc_ecma_ast::BlockStmtOrExpr::BlockStmt(
                                        func.body.context("in getting the body")?,
                                    )),
                                    is_async: func.is_async,
                                    is_generator: func.is_generator,
                                    type_params: None,
                                    return_type: None,
                                })
                            }
                        }
                    },
                    crate::Item::Lit { lit } => Expr::Lit(lit.clone()),
                    Item::New { class, args } => {
                        mark = true;
                        Expr::New(NewExpr {
                            span,
                            ctxt: SyntaxContext::empty(),
                            callee: sr(class),
                            type_args: None,
                            args: Some(
                                args.iter()
                                    .map(&mut sr)
                                    .map(|e| ExprOrSpread {
                                        spread: None,
                                        expr: e,
                                    })
                                    .collect(),
                            ),
                        })
                    }
                    crate::Item::Call { callee, args } => {
                        mark = true;
                        Expr::Call(CallExpr {
                            span: span,
                            ctxt: SyntaxContext::empty(),
                            callee: 'a: {
                                swc_ecma_ast::Callee::Expr(match callee {
                                    crate::TCallee::Member { func: r#fn, member } => {
                                        let f = sr(r#fn);
                                        Box::new(Expr::Member(MemberExpr {
                                            span: span,
                                            obj: f,
                                            prop: swc_ecma_ast::MemberProp::Computed(
                                                ComputedPropName {
                                                    span: span,
                                                    expr: sr(member),
                                                },
                                            ),
                                        }))
                                    }
                                    TCallee::PrivateMember { func: r#fn, member } => {
                                        let f = sr(r#fn);
                                        Box::new(Expr::Member(MemberExpr {
                                            span: span,
                                            obj: f,
                                            prop: swc_ecma_ast::MemberProp::PrivateName(
                                                PrivateName {
                                                    span,
                                                    name: member.sym.clone(),
                                                },
                                            ),
                                        }))
                                    }
                                    TCallee::Val(r#fn) => {
                                        let f = sr(r#fn);
                                        f
                                    }
                                    TCallee::Import => {
                                        break 'a Callee::Import(swc_ecma_ast::Import {
                                            span,
                                            phase: Default::default(),
                                        });
                                    }
                                    TCallee::Super => {
                                        break 'a Callee::Super(swc_ecma_ast::Super {
                                            span,
                                            // phase: Default::default(),
                                        });
                                    }
                                })
                            },
                            args: args
                                .iter()
                                .map(|a| swc_ecma_ast::ExprOrSpread {
                                    spread: None,
                                    expr: sr(a),
                                })
                                .collect(),
                            type_args: None,
                        })
                    }
                    crate::Item::Obj { members } => Expr::Object(ObjectLit {
                        span: span,
                        props: members
                            .iter()
                            .map(|a| {
                                Ok(PropOrSpread::Prop({
                                    let name = match &a.0 {
                                        crate::PropKey::Lit(l) => {
                                            swc_ecma_ast::PropName::Ident(swc_ecma_ast::IdentName {
                                                span: span,
                                                sym: l.0.clone(),
                                            })
                                        }
                                        crate::PropKey::Computed(c) => {
                                            swc_ecma_ast::PropName::Computed(ComputedPropName {
                                                span: span,
                                                expr: sr(c),
                                            })
                                        }
                                    };
                                    Box::new(match &a.1 {
                                        crate::PropVal::Item(i) => Prop::KeyValue(KeyValueProp {
                                            key: name,
                                            value: sr(i),
                                        }),
                                        crate::PropVal::Getter(g) => Prop::Getter(GetterProp {
                                            span,
                                            key: name,
                                            type_ann: None,
                                            body: {
                                                let f: Function = g.try_into()?;
                                                f.body
                                            },
                                        }),
                                        crate::PropVal::Setter(s) => Prop::Setter({
                                            let f: Function = s.try_into()?;
                                            SetterProp {
                                                span,
                                                key: name,
                                                this_param: None,
                                                param: Box::new(
                                                    f.params
                                                        .get(0)
                                                        .map(|g| &g.pat)
                                                        .cloned()
                                                        .context("in getting the param")?,
                                                ),
                                                body: f.body,
                                            }
                                        }),
                                        crate::PropVal::Method(s) => Prop::Method({
                                            let f: Function = s.try_into()?;
                                            MethodProp {
                                                key: name,
                                                function: Box::new(f),
                                            }
                                        }),
                                    })
                                }))
                            })
                            .collect::<Result<_, anyhow::Error>>()?,
                    }),
                    Item::Class {
                        superclass,
                        members,
                        constructor,
                    } => Expr::Class(ClassExpr {
                        ident: None,
                        class: Box::new(Class {
                            span,
                            ctxt: Default::default(),
                            decorators: vec![],
                            super_class: superclass.as_ref().map(|a| sr(a)),
                            is_abstract: false,
                            type_params: None,
                            super_type_params: None,
                            implements: Default::default(),
                            body: members
                                .iter()
                                .map(|a| {
                                    Ok({
                                        let name = match &a.1 {
                                            crate::PropKey::Lit(l) => {
                                                swc_ecma_ast::PropName::Ident(
                                                    swc_ecma_ast::IdentName {
                                                        span: span,
                                                        sym: l.0.clone(),
                                                    },
                                                )
                                            }
                                            crate::PropKey::Computed(c) => {
                                                swc_ecma_ast::PropName::Computed(ComputedPropName {
                                                    span: span,
                                                    expr: sr(c),
                                                })
                                            }
                                        };
                                        match &a.2 {
                                            crate::PropVal::Item(i) => {
                                                if a.0.contains(MemberFlags::PRIVATE) {
                                                    ClassMember::PrivateProp(PrivateProp {
                                                        span,
                                                        ctxt: Default::default(),
                                                        key: match &a.1 {
                                                            PropKey::Lit(l) => PrivateName {
                                                                name: l.0.clone(),
                                                                span,
                                                            },
                                                            _ => anyhow::bail!(
                                                                "invalid private name"
                                                            ),
                                                        },
                                                        value: match i.as_ref() {
                                                            None => None,
                                                            Some(a) => Some(sr(a)),
                                                        },
                                                        type_ann: None,
                                                        is_static: a
                                                            .0
                                                            .contains(MemberFlags::STATIC),
                                                        decorators: Default::default(),
                                                        accessibility: None,
                                                        // is_abstract: false,
                                                        is_optional: false,
                                                        is_override: false,
                                                        readonly: false,
                                                        // declare: false,
                                                        definite: false,
                                                    })
                                                } else {
                                                    ClassMember::ClassProp(ClassProp {
                                                        span,
                                                        key: name,
                                                        value: match i.as_ref() {
                                                            None => None,
                                                            Some(a) => Some(sr(a)),
                                                        },
                                                        type_ann: None,
                                                        is_static: a
                                                            .0
                                                            .contains(MemberFlags::STATIC),
                                                        decorators: Default::default(),
                                                        accessibility: None,
                                                        is_abstract: false,
                                                        is_optional: false,
                                                        is_override: false,
                                                        readonly: false,
                                                        declare: false,
                                                        definite: false,
                                                    })
                                                }
                                            }
                                            crate::PropVal::Getter(m) => {
                                                if a.0.contains(MemberFlags::PRIVATE) {
                                                    swc_ecma_ast::ClassMember::PrivateMethod(
                                                        PrivateMethod {
                                                            span,
                                                            key: match &a.1 {
                                                                PropKey::Lit(l) => PrivateName {
                                                                    name: l.0.clone(),
                                                                    span,
                                                                },
                                                                _ => anyhow::bail!(
                                                                    "invalid private name"
                                                                ),
                                                            },
                                                            function: Box::new(m.try_into()?),
                                                            kind: swc_ecma_ast::MethodKind::Getter,
                                                            is_static: a
                                                                .0
                                                                .contains(MemberFlags::STATIC),
                                                            accessibility: None,
                                                            is_abstract: false,
                                                            is_optional: false,
                                                            is_override: false,
                                                        },
                                                    )
                                                } else {
                                                    swc_ecma_ast::ClassMember::Method(ClassMethod {
                                                        span,
                                                        key: name,
                                                        function: Box::new(m.try_into()?),
                                                        kind: swc_ecma_ast::MethodKind::Getter,
                                                        is_static: a
                                                            .0
                                                            .contains(MemberFlags::STATIC),
                                                        accessibility: None,
                                                        is_abstract: false,
                                                        is_optional: false,
                                                        is_override: false,
                                                    })
                                                }
                                            }
                                            crate::PropVal::Setter(m) => {
                                                if a.0.contains(MemberFlags::PRIVATE) {
                                                    swc_ecma_ast::ClassMember::PrivateMethod(
                                                        PrivateMethod {
                                                            span,
                                                            key: match &a.1 {
                                                                PropKey::Lit(l) => PrivateName {
                                                                    name: l.0.clone(),
                                                                    span,
                                                                },
                                                                _ => anyhow::bail!(
                                                                    "invalid private name"
                                                                ),
                                                            },
                                                            function: Box::new(m.try_into()?),
                                                            kind: swc_ecma_ast::MethodKind::Setter,
                                                            is_static: a
                                                                .0
                                                                .contains(MemberFlags::STATIC),
                                                            accessibility: None,
                                                            is_abstract: false,
                                                            is_optional: false,
                                                            is_override: false,
                                                        },
                                                    )
                                                } else {
                                                    swc_ecma_ast::ClassMember::Method(ClassMethod {
                                                        span,
                                                        key: name,
                                                        function: Box::new(m.try_into()?),
                                                        kind: swc_ecma_ast::MethodKind::Setter,
                                                        is_static: a
                                                            .0
                                                            .contains(MemberFlags::STATIC),
                                                        accessibility: None,
                                                        is_abstract: false,
                                                        is_optional: false,
                                                        is_override: false,
                                                    })
                                                }
                                            }
                                            crate::PropVal::Method(m) => {
                                                if a.0.contains(MemberFlags::PRIVATE) {
                                                    swc_ecma_ast::ClassMember::PrivateMethod(
                                                        PrivateMethod {
                                                            span,
                                                            key: match &a.1 {
                                                                PropKey::Lit(l) => PrivateName {
                                                                    name: l.0.clone(),
                                                                    span,
                                                                },
                                                                _ => anyhow::bail!(
                                                                    "invalid private name"
                                                                ),
                                                            },
                                                            function: Box::new(m.try_into()?),
                                                            kind: swc_ecma_ast::MethodKind::Method,
                                                            is_static: a
                                                                .0
                                                                .contains(MemberFlags::STATIC),
                                                            accessibility: None,
                                                            is_abstract: false,
                                                            is_optional: false,
                                                            is_override: false,
                                                        },
                                                    )
                                                } else {
                                                    swc_ecma_ast::ClassMember::Method(ClassMethod {
                                                        span,
                                                        key: name,
                                                        function: Box::new(m.try_into()?),
                                                        kind: swc_ecma_ast::MethodKind::Method,
                                                        is_static: a
                                                            .0
                                                            .contains(MemberFlags::STATIC),
                                                        accessibility: None,
                                                        is_abstract: false,
                                                        is_optional: false,
                                                        is_override: false,
                                                    })
                                                }
                                            }
                                        }
                                    })
                                })
                                .chain(constructor.iter().map(|x| {
                                    let x: Function = x.try_into()?;
                                    Ok(ClassMember::Constructor(Constructor {
                                        span: x.span,
                                        ctxt: x.ctxt,
                                        key: swc_ecma_ast::PropName::Ident(IdentName {
                                            span: x.span,
                                            sym: Atom::new("constructor"),
                                        }),
                                        params: x
                                            .params
                                            .into_iter()
                                            .map(ParamOrTsParamProp::Param)
                                            .collect(),
                                        body: x.body,
                                        accessibility: None,
                                        is_optional: false,
                                    }))
                                }))
                                .collect::<Result<_, anyhow::Error>>()?,
                        }),
                    }),
                    crate::Item::Arr { members } => Expr::Array(ArrayLit {
                        span: span,
                        elems: members
                            .iter()
                            .map(|a| {
                                Some(ExprOrSpread {
                                    spread: None,
                                    expr: sr(a),
                                })
                            })
                            .collect(),
                    }),
                    crate::Item::Yield { value, delegate } => {
                        mark = true;
                        Expr::Yield(swc_ecma_ast::YieldExpr {
                            span: span,
                            arg: value.as_ref().map(|yielded_value| sr(yielded_value)),
                            delegate: *delegate,
                        })
                    }
                    crate::Item::Await { value } => {
                        mark = true;
                        Expr::Await(swc_ecma_ast::AwaitExpr {
                            span: span,
                            arg: sr(value),
                        })
                    }
                    crate::Item::Undef => *Expr::undefined(span),
                    crate::Item::Asm { value } => match value {
                        portal_jsc_common::Asm::OrZero(a) => Expr::Bin(BinExpr {
                            span,
                            op: BinaryOp::BitOr,
                            left: sr(a),
                            right: Box::new(Expr::Lit(Lit::Num(Number {
                                span,
                                value: 0.0,
                                raw: None,
                            }))),
                        }),
                        _ => todo!(),
                    },
                    crate::Item::This => Expr::This(ThisExpr { span }),
                    // Item::Intrinsic { value } => {
                    //     let mut v = Vec::default();
                    //     let x = value
                    //         .as_ref()
                    //         .map(&mut |a| Ok::<_, Infallible>(v.push(sr(a))))
                    //         .unwrap();
                    //     Expr::Call(CallExpr {
                    //         span,
                    //         ctxt: Default::default(),
                    //         callee: swc_ecma_ast::Callee::Expr(Box::new(Expr::Member(
                    //             MemberExpr {
                    //                 span,
                    //                 obj: Box::new(Expr::Ident(ident(
                    //                     &(Atom::new("globalThis"), Default::default()),
                    //                     span,
                    //                 ))),
                    //                 prop: swc_ecma_ast::MemberProp::Computed(ComputedPropName {
                    //                     span,
                    //                     expr: Box::new(Expr::Lit(Lit::Str(Str {
                    //                         span,
                    //                         raw: None,
                    //                         value: Atom::new(x.key()),
                    //                     }))),
                    //                 }),
                    //             },
                    //         ))),
                    //         args: v
                    //             .into_iter()
                    //             .map(|a| ExprOrSpread {
                    //                 expr: a,
                    //                 spread: None,
                    //             })
                    //             .collect(),
                    //         type_args: None,
                    //     })
                    // }
                });
                if !mark {
                    if let AssignTarget::Simple(SimpleAssignTarget::Ident(i)) = &left {
                        if state.contains_key(&i.to_id()) {
                        } else {
                            state.insert(i.to_id(), right);
                            ids.push(i.to_id());
                            continue;
                        }
                    }
                }
                flush!();
                cfg.blocks[new_block_id].stmts.push(Stmt::Expr(ExprStmt {
                    span: span,
                    expr: Box::new(Expr::Assign(AssignExpr {
                        span: span,
                        op: swc_ecma_ast::AssignOp::Assign,
                        left,
                        right,
                    })),
                }));
            }
            flush!();
            let term = match &tcfg.blocks[block_id].post.term {
                crate::TTerm::Return(r) => Term::Return(
                    r.as_ref()
                        .map(|returned_value| {
                            ident(
                                returned_value,
                                tcfg.blocks[block_id]
                                    .post
                                    .orig_span
                                    .clone()
                                    .unwrap_or(Span::dummy_with_cmt()),
                            )
                        })
                        .map(Expr::Ident),
                ),
                crate::TTerm::Throw(x) => Term::Throw(Expr::Ident(ident(
                    x,
                    tcfg.blocks[block_id]
                        .post
                        .orig_span
                        .clone()
                        .unwrap_or(Span::dummy_with_cmt()),
                ))),
                crate::TTerm::Jmp(id) => Term::Jmp(self.trans(cfg, tcfg, *id)?),
                crate::TTerm::CondJmp {
                    cond,
                    if_true,
                    if_false,
                } => Term::CondJmp {
                    cond: Expr::Ident(ident(
                        cond,
                        tcfg.blocks[block_id]
                            .post
                            .orig_span
                            .clone()
                            .unwrap_or(Span::dummy_with_cmt()),
                    )),
                    if_true: self.trans(cfg, tcfg, *if_true)?,
                    if_false: self.trans(cfg, tcfg, *if_false)?,
                },
                crate::TTerm::Switch { x, blocks, default } => Term::Switch {
                    x: Expr::Ident(ident(
                        x,
                        tcfg.blocks[block_id]
                            .post
                            .orig_span
                            .clone()
                            .unwrap_or(Span::dummy_with_cmt()),
                    )),
                    blocks: blocks
                        .iter()
                        .map(|a| {
                            anyhow::Ok((
                                Expr::Ident(ident(
                                    a.0,
                                    tcfg.blocks[block_id]
                                        .post
                                        .orig_span
                                        .clone()
                                        .unwrap_or(Span::dummy_with_cmt()),
                                )),
                                self.trans(cfg, tcfg, *a.1)?,
                            ))
                        })
                        .collect::<anyhow::Result<_>>()?,
                    default: self.trans(cfg, tcfg, *default)?,
                },
                crate::TTerm::Default => Term::Default,
            };
            cfg.blocks[new_block_id].end.term = term;
        }
    }
}
fn ident(a: &Ident, span: Span) -> swc_ecma_ast::Ident {
    swc_ecma_ast::Ident {
        span: span,
        ctxt: a.1.clone(),
        sym: a.0.clone(),
        optional: false,
    }
}
