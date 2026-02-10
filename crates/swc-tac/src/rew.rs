//! Rewriting TAC back to CFG/JavaScript.
//!
//! This module provides functionality to convert TAC (Three-Address Code) back
//! to CFG (Control Flow Graph) or JavaScript AST representations. This is useful
//! for code generation after optimization passes.
//!
//! # Rewriting Process
//!
//! The rewriting process:
//! 1. Converts TAC items back to SWC AST expressions
//! 2. Reconstructs complex expressions from simple assignments
//! 3. Generates JavaScript code from the TAC representation
//! 4. Preserves semantic information and type annotations
//!
//! # Key Types
//!
//! - [`Options`]: Configuration for the rewriting process

use crate::{Item, LId, MemberFlags, PropKey, SpreadOr, TBlock, TBlockId, TCallee, TCfg, TFunc};
use anyhow::Context;
use portal_jsc_common::syntax::Asm;
use portal_jsc_swc_util::SemanticCfg;
use std::collections::{BTreeMap, HashMap};
use std::convert::Infallible;
use std::mem::take;
use swc_atoms::Atom;
use swc_cfg::{Block, Cfg};
use swc_cfg::{Func, Term};
use swc_common::{Span, Spanned, SyntaxContext};
use swc_ecma_ast::{
    ArrayLit, ArrayPat, CondExpr, KeyValuePatProp, MetaPropExpr, NewExpr, ObjectPat, ObjectPatProp,
    Param, PrivateMethod, PrivateName, RestPat, UnaryOp,
};
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
use swc_ll_common::{PrivateKind, PropSym, TClass};

/// Options for TAC to CFG/JavaScript rewriting.
///
/// Provides configuration for how TAC should be converted back to
/// higher-level representations.
///
/// # Fields
///
/// - `semantic`: Semantic configuration for the conversion
/// - `conf`: Function to convert Func to Function (CFG to AST)
#[non_exhaustive]
#[derive(Clone)]
pub struct Options<'a> {
    /// Semantic configuration controlling conversion behavior
    pub semantic: &'a SemanticCfg,
    /// Function to convert CFG Func to AST Function
    pub conf: &'a (dyn Fn(Func) -> anyhow::Result<Function> + 'a),
}
impl Options<'static> {
    pub fn bud<T>(func: impl FnOnce(&Options<'_>) -> T) -> T {
        return func(&Options {
            semantic: &SemanticCfg::default(),
            conf: &|f| Ok(f.into()),
        });
    }
}
impl TFunc {
    pub fn to_func_with_options(&self, options: &Options<'_>) -> anyhow::Result<Func> {
        let value = self;
        let mut cfg = Cfg::default();
        let entry = Rew {
            all: BTreeMap::new(),
            options,
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
impl<'a> TryFrom<&'a TFunc> for Func {
    type Error = anyhow::Error;
    fn try_from(value: &'a TFunc) -> Result<Self, Self::Error> {
        Options::bud(|opts| value.to_func_with_options(opts))
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
pub trait Render<I, F> {
    type Result;
    fn render<Cx, E>(
        &self,
        mark: &mut bool,
        span: Span,
        cx: &mut Cx,
        sr: &mut (dyn FnMut(&mut Cx, &I) -> Result<Box<Expr>, E> + '_),
        si: &mut (dyn FnMut(&mut Cx, &I) -> Result<swc_ecma_ast::Ident, E> + '_),
        sf: &mut (dyn FnMut(&mut Cx, &F) -> Result<Function, E> + '_),
    ) -> Result<Self::Result, E>;
}
impl<I, F> Render<I, F> for Item<I, F> {
    type Result = Box<Expr>;
    fn render<Cx, E>(
        &self,
        mark: &mut bool,
        span: Span,
        cx: &mut Cx,
        sr: &mut (dyn FnMut(&mut Cx, &I) -> Result<Box<Expr>, E> + '_),
        si: &mut (dyn FnMut(&mut Cx, &I) -> Result<swc_ecma_ast::Ident, E> + '_),
        sf: &mut (dyn FnMut(&mut Cx, &F) -> Result<Function, E> + '_),
    ) -> Result<Box<Expr>, E> {
        let right = Box::new(match self {
            Item::Meta { prop } => Expr::MetaProp(MetaPropExpr { span, kind: *prop }),
            Item::Arguments => Expr::Ident(swc_ecma_ast::Ident {
                span,
                ctxt: Default::default(),
                sym: Atom::new("arguments"),
                optional: false,
            }),
            Item::Select {
                cond,
                then,
                otherwise,
            } => {
                let mut temps = Vec::default();
                match 'a: {
                    // let mut b = true;
                    let mut i = 0;
                    let temp = || swc_ecma_ast::Ident::new_private(Atom::new("temp"), span);
                    Box::new(Expr::Seq(SeqExpr {
                        span,
                        exprs: match [cond, then, otherwise]
                            .map(|a| match sr(cx, a) {
                                s => s.map(|s| {
                                    Box::new(Expr::Assign(AssignExpr {
                                        span,
                                        op: AssignOp::Assign,
                                        left: AssignTarget::Simple(SimpleAssignTarget::Ident({
                                            let t = temp();
                                            temps.push(t.clone());
                                            t.into()
                                        })),
                                        right: s,
                                    }))
                                }),
                            })
                            .into_iter()
                            // .flatten()
                            .chain([Ok(Box::new(Expr::Ident(temps.remove(0))))])
                            .collect::<Result<Vec<_>, E>>()?
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
                        cons: temps.remove(0).into(),
                        alt: temps.remove(0).into(),
                    }),
                }
            }
            crate::Item::Just { id } => return si(cx, id).map(|a| a.into()),
            crate::Item::Bin { left, right, op } => Expr::Bin(BinExpr {
                span: span,
                op: *op,
                left: sr(cx, left)?,
                right: sr(cx, right)?,
            }),
            Item::HasPrivateMem { obj, mem } => Expr::Bin(BinExpr {
                span,
                op: BinaryOp::In,
                left: Box::new(Expr::PrivateName(PrivateName {
                    span: mem.span,
                    name: mem.sym.clone(),
                })),
                right: sr(cx, obj)?,
            }),
            crate::Item::Un { arg, op } => Expr::Unary(UnaryExpr {
                span: span,
                op: *op,
                arg: sr(cx, arg)?,
            }),
            crate::Item::Mem { obj, mem } => {
                // let obj = ident(obj, span);
                // let mem = ident(mem, span);
                *mark = true;
                Expr::Member(MemberExpr {
                    span: span,
                    obj: sr(cx, obj)?,
                    prop: swc_ecma_ast::MemberProp::Computed(swc_ecma_ast::ComputedPropName {
                        span: span,
                        expr: sr(cx, mem)?,
                    }),
                })
            }
            Item::PrivateMem { obj, mem } => Expr::Member(MemberExpr {
                span: span,
                obj: sr(cx, obj)?,
                prop: swc_ecma_ast::MemberProp::PrivateName(PrivateName {
                    span: mem.span,
                    name: mem.sym.clone(),
                }),
            }),
            crate::Item::Func { func, arrow } => match sf(cx, func)? {
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
                                func.body.unwrap(),
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
                *mark = true;
                Expr::New(NewExpr {
                    span,
                    ctxt: SyntaxContext::empty(),
                    callee: sr(cx, class)?,
                    type_args: None,
                    args: Some(
                        args.iter()
                            .map(|a| sr(cx, a))
                            .map(|e| {
                                e.map(|e| ExprOrSpread {
                                    spread: None,
                                    expr: e,
                                })
                            })
                            .collect::<Result<_, E>>()?,
                    ),
                })
            }
            crate::Item::Call { callee, args } => {
                *mark = true;
                Expr::Call(CallExpr {
                    span: span,
                    ctxt: SyntaxContext::empty(),
                    callee: 'a: {
                        swc_ecma_ast::Callee::Expr(match callee {
                            crate::TCallee::Member { func: r#fn, member } => {
                                let f = sr(cx, r#fn)?;
                                Box::new(Expr::Member(MemberExpr {
                                    span: span,
                                    obj: f,
                                    prop: swc_ecma_ast::MemberProp::Computed(ComputedPropName {
                                        span: span,
                                        expr: sr(cx, member)?,
                                    }),
                                }))
                            }
                            TCallee::PrivateMember { func: r#fn, member } => {
                                let f = sr(cx, r#fn)?;
                                Box::new(Expr::Member(MemberExpr {
                                    span: span,
                                    obj: f,
                                    prop: swc_ecma_ast::MemberProp::PrivateName(PrivateName {
                                        span,
                                        name: member.sym.clone(),
                                    }),
                                }))
                            }
                            TCallee::Val(r#fn) => {
                                let f = sr(cx, r#fn)?;
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
                            TCallee::Eval => Box::new(Expr::Ident(swc_ecma_ast::Ident::new(
                                Atom::new("eval"),
                                span,
                                Default::default(),
                            ))),
                        })
                    },
                    args: args
                        .iter()
                        .map(
                            |SpreadOr {
                                 value: a,
                                 is_spread: s,
                             }| {
                                Ok::<_, E>(swc_ecma_ast::ExprOrSpread {
                                    spread: s.then(|| span),
                                    expr: sr(cx, a)?,
                                })
                            },
                        )
                        .collect::<Result<_, E>>()?,
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
                                crate::PropKey::Lit(PropSym {
                                    sym: l,
                                    span,
                                    ctx: _,
                                }) => swc_ecma_ast::PropName::Ident(swc_ecma_ast::IdentName {
                                    span: *span,
                                    sym: l.clone(),
                                }),
                                crate::PropKey::Computed(c) => {
                                    swc_ecma_ast::PropName::Computed(ComputedPropName {
                                        span: span,
                                        expr: sr(cx, c)?,
                                    })
                                }
                                _ => todo!(),
                            };
                            Box::new(match &a.1 {
                                crate::PropVal::Item(i) => Prop::KeyValue(KeyValueProp {
                                    key: name,
                                    value: sr(cx, i)?,
                                }),
                                crate::PropVal::Getter(g) => Prop::Getter(GetterProp {
                                    span,
                                    key: name,
                                    type_ann: None,
                                    body: {
                                        let f: Function = sf(cx, g)?;
                                        f.body
                                    },
                                }),
                                crate::PropVal::Setter(s) => Prop::Setter({
                                    let f: Function = sf(cx, s)?;
                                    SetterProp {
                                        span,
                                        key: name,
                                        this_param: None,
                                        param: Box::new(
                                            f.params.get(0).map(|g| &g.pat).cloned().unwrap(),
                                        ),
                                        body: f.body,
                                    }
                                }),
                                crate::PropVal::Method(s) => Prop::Method({
                                    let f: Function = sf(cx, s)?;
                                    MethodProp {
                                        key: name,
                                        function: Box::new(f),
                                    }
                                }),
                                _ => todo!(),
                            })
                        }))
                    })
                    .collect::<Result<_, E>>()?,
            }),
            Item::Class(TClass{
                superclass,
                members,
                constructor,
            }) => Expr::Class(ClassExpr {
                ident: None,
                class: Box::new(Class {
                    span,
                    ctxt: Default::default(),
                    decorators: vec![],
                    super_class: superclass.as_ref().map(|a| sr(cx, a)).transpose()?,
                    is_abstract: false,
                    type_params: None,
                    super_type_params: None,
                    implements: Default::default(),
                    body: members
                        .iter()
                        .map(|a| {
                            Ok({
                                let name = match &a.1 {
                                    crate::PropKey::Lit(PropSym {
                                        sym: l,
                                        span,
                                        ctx: _,
                                    }) => swc_ecma_ast::PropName::Ident(swc_ecma_ast::IdentName {
                                        span: *span,
                                        sym: l.clone(),
                                    }),
                                    crate::PropKey::Computed(c) => {
                                        swc_ecma_ast::PropName::Computed(ComputedPropName {
                                            span: span,
                                            expr: sr(cx, c)?,
                                        })
                                    }
                                    _ => todo!(),
                                };
                                match &a.2 {
                                    crate::PropVal::Item(i) => {
                                        match &a.1 {
                                            PropKey::Lit(PropSym {
                                                sym: _,
                                                span: _,
                                                ctx: PrivateKind::Private(ctx),
                                            }) => {
                                                ClassMember::PrivateProp(PrivateProp {
                                                    span,
                                                    ctxt: Default::default(),
                                                    key: match &a.1 {
                                                        PropKey::Lit(PropSym {
                                                            sym: l,
                                                            span,
                                                            ctx: _,
                                                        }) => PrivateName {
                                                            name: l.clone(),
                                                            span: *span,
                                                        },
                                                        _ => panic!("invalid private name"),
                                                    },
                                                    value: match i.as_ref() {
                                                        None => None,
                                                        Some(a) => Some(sr(cx, a)?),
                                                    },
                                                    type_ann: None,
                                                    is_static: a.0.contains(MemberFlags::STATIC),
                                                    decorators: Default::default(),
                                                    accessibility: None,
                                                    // is_abstract: false,
                                                    is_optional: false,
                                                    is_override: false,
                                                    readonly: false,
                                                    // declare: false,
                                                    definite: false,
                                                })
                                            }
                                            _ => ClassMember::ClassProp(ClassProp {
                                                span,
                                                key: name,
                                                value: match i.as_ref() {
                                                    None => None,
                                                    Some(a) => Some(sr(cx, a)?),
                                                },
                                                type_ann: None,
                                                is_static: a.0.contains(MemberFlags::STATIC),
                                                decorators: Default::default(),
                                                accessibility: None,
                                                is_abstract: false,
                                                is_optional: false,
                                                is_override: false,
                                                readonly: false,
                                                declare: false,
                                                definite: false,
                                            }),
                                        }
                                    }
                                    crate::PropVal::Getter(m) => match &a.1 {
                                        PropKey::Lit(PropSym {
                                            sym: _,
                                            span: _,
                                            ctx: PrivateKind::Private(ctx),
                                        }) => swc_ecma_ast::ClassMember::PrivateMethod(
                                            PrivateMethod {
                                                span,
                                                key: match &a.1 {
                                                    PropKey::Lit(PropSym {
                                                        sym: l,
                                                        span,
                                                        ctx: _,
                                                    }) => PrivateName {
                                                        name: l.clone(),
                                                        span: *span,
                                                    },
                                                    _ => panic!("invalid private name"),
                                                },
                                                function: Box::new(sf(cx, m)?),
                                                kind: swc_ecma_ast::MethodKind::Getter,
                                                is_static: a.0.contains(MemberFlags::STATIC),
                                                accessibility: None,
                                                is_abstract: false,
                                                is_optional: false,
                                                is_override: false,
                                            },
                                        ),
                                        _ => swc_ecma_ast::ClassMember::Method(ClassMethod {
                                            span,
                                            key: name,
                                            function: Box::new(sf(cx, m)?),
                                            kind: swc_ecma_ast::MethodKind::Getter,
                                            is_static: a.0.contains(MemberFlags::STATIC),
                                            accessibility: None,
                                            is_abstract: false,
                                            is_optional: false,
                                            is_override: false,
                                        }),
                                    },
                                    crate::PropVal::Setter(m) => match &a.1 {
                                        PropKey::Lit(PropSym {
                                            sym: _,
                                            span: _,
                                            ctx: PrivateKind::Private(ctx),
                                        }) => swc_ecma_ast::ClassMember::PrivateMethod(
                                            PrivateMethod {
                                                span,
                                                key: match &a.1 {
                                                    PropKey::Lit(PropSym {
                                                        sym: l,
                                                        span,
                                                        ctx: _,
                                                    }) => PrivateName {
                                                        name: l.clone(),
                                                        span: *span,
                                                    },
                                                    _ => panic!("invalid private name"),
                                                },
                                                function: Box::new(sf(cx, m)?),
                                                kind: swc_ecma_ast::MethodKind::Setter,
                                                is_static: a.0.contains(MemberFlags::STATIC),
                                                accessibility: None,
                                                is_abstract: false,
                                                is_optional: false,
                                                is_override: false,
                                            },
                                        ),
                                        _ => swc_ecma_ast::ClassMember::Method(ClassMethod {
                                            span,
                                            key: name,
                                            function: Box::new(sf(cx, m)?),
                                            kind: swc_ecma_ast::MethodKind::Setter,
                                            is_static: a.0.contains(MemberFlags::STATIC),
                                            accessibility: None,
                                            is_abstract: false,
                                            is_optional: false,
                                            is_override: false,
                                        }),
                                    },
                                    crate::PropVal::Method(m) => match &a.1 {
                                        PropKey::Lit(PropSym {
                                            sym: _,
                                            span: _,
                                            ctx: PrivateKind::Private(ctx),
                                        }) => swc_ecma_ast::ClassMember::PrivateMethod(
                                            PrivateMethod {
                                                span,
                                                key: match &a.1 {
                                                    PropKey::Lit(PropSym {
                                                        sym: l,
                                                        span,
                                                        ctx: _,
                                                    }) => PrivateName {
                                                        name: l.clone(),
                                                        span: *span,
                                                    },
                                                    _ => panic!("invalid private name"),
                                                },
                                                function: Box::new(sf(cx, m)?),
                                                kind: swc_ecma_ast::MethodKind::Method,
                                                is_static: a.0.contains(MemberFlags::STATIC),
                                                accessibility: None,
                                                is_abstract: false,
                                                is_optional: false,
                                                is_override: false,
                                            },
                                        ),
                                        _ => swc_ecma_ast::ClassMember::Method(ClassMethod {
                                            span,
                                            key: name,
                                            function: Box::new(sf(cx, m)?),
                                            kind: swc_ecma_ast::MethodKind::Method,
                                            is_static: a.0.contains(MemberFlags::STATIC),
                                            accessibility: None,
                                            is_abstract: false,
                                            is_optional: false,
                                            is_override: false,
                                        }),
                                    },
                                    _ => todo!(),
                                }
                            })
                        })
                        .collect::<Vec<_>>()
                        .into_iter()
                        .chain(constructor.iter().map(|x| {
                            let x: Function = sf(cx, x)?;
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
                        .collect::<Result<_, E>>()?,
                }),
            }),
            crate::Item::Arr { members } => Expr::Array(ArrayLit {
                span: span,
                elems: members
                    .iter()
                    .map(
                        |SpreadOr {
                             value: a,
                             is_spread: b,
                         }| {
                            Ok(Some(ExprOrSpread {
                                spread: b.then(|| span),
                                expr: sr(cx, a)?,
                            }))
                        },
                    )
                    .collect::<Result<_, E>>()?,
            }),
            crate::Item::Yield { value, delegate } => {
                *mark = true;
                Expr::Yield(swc_ecma_ast::YieldExpr {
                    span: span,
                    arg: value
                        .as_ref()
                        .map(|yielded_value| sr(cx, yielded_value))
                        .transpose()?,
                    delegate: *delegate,
                })
            }
            crate::Item::Await { value } => {
                *mark = true;
                Expr::Await(swc_ecma_ast::AwaitExpr {
                    span: span,
                    arg: sr(cx, value)?,
                })
            }
            crate::Item::Undef => *Expr::undefined(span),
            crate::Item::Asm { value } => match value {
                Asm::OrZero(a) => Expr::Bin(BinExpr {
                    span,
                    op: BinaryOp::BitOr,
                    left: sr(cx, a)?,
                    right: Box::new(Expr::Lit(Lit::Num(Number {
                        span,
                        value: 0.0,
                        raw: None,
                    }))),
                }),
                _ => todo!(),
            },
            crate::Item::This => Expr::This(ThisExpr { span }),
            Item::StaticSubArray {
                begin,
                end,
                wrapped,
            } => {
                let rest = swc_ecma_ast::Ident::new_private(Atom::new("rest"), span);
                let any = || swc_ecma_ast::Ident::new_private(Atom::new("ignored"), span);
                let end = (0..*end).map(|_| any()).collect::<Vec<_>>();
                Expr::Call(CallExpr {
                    span,
                    ctxt: Default::default(),
                    callee: Callee::Expr(Box::new(Expr::Arrow(ArrowExpr {
                        span,
                        ctxt: Default::default(),
                        params: [Pat::Array(ArrayPat {
                            span,
                            optional: false,
                            type_ann: None,
                            elems: (0..*begin)
                                .map(|_| Pat::Ident(any().into()))
                                .chain([Pat::Rest(RestPat {
                                    span,
                                    dot3_token: span,
                                    type_ann: None,
                                    arg: Box::new(Pat::Ident(rest.clone().into())),
                                })])
                                .chain(end.iter().cloned().map(|a| Pat::Ident(a.into())))
                                .map(Some)
                                .collect(),
                        })]
                        .into_iter()
                        .collect(),
                        body: Box::new(swc_ecma_ast::BlockStmtOrExpr::Expr(if end.len() == 0 {
                            rest.into()
                        } else {
                            Box::new(Expr::Array(ArrayLit {
                                span,
                                elems: end
                                    .into_iter()
                                    .map(|a| {
                                        Some(ExprOrSpread {
                                            expr: a.into(),
                                            spread: None,
                                        })
                                    })
                                    .chain([Some(ExprOrSpread {
                                        spread: Some(span),
                                        expr: rest.into(),
                                    })])
                                    .collect(),
                            }))
                        })),
                        is_async: false,
                        is_generator: false,
                        type_params: None,
                        return_type: None,
                    }))),
                    args: [ExprOrSpread {
                        expr: sr(cx, wrapped)?,
                        spread: None,
                    }]
                    .into_iter()
                    .collect(),
                    type_args: None,
                })
            }
            Item::StaticSubObject { wrapped, keys } => {
                let rest = swc_ecma_ast::Ident::new_private(Atom::new("rest"), span);
                let any = || swc_ecma_ast::Ident::new_private(Atom::new("ignored"), span);
                Expr::Call(CallExpr {
                    span,
                    ctxt: Default::default(),
                    callee: Callee::Expr(Box::new(Expr::Arrow(ArrowExpr {
                        span,
                        ctxt: Default::default(),
                        params: [Pat::Object(ObjectPat {
                            span,
                            optional: false,
                            type_ann: None,
                            props: keys
                                .iter()
                                .map(|k| {
                                    Ok(ObjectPatProp::KeyValue(KeyValuePatProp {
                                        key: match &*k {
                                            crate::PropKey::Lit(PropSym {
                                                sym: l,
                                                span,
                                                ctx: _,
                                            }) => swc_ecma_ast::PropName::Ident(
                                                swc_ecma_ast::IdentName {
                                                    span: *span,
                                                    sym: l.clone(),
                                                },
                                            ),
                                            crate::PropKey::Computed(c) => {
                                                swc_ecma_ast::PropName::Computed(ComputedPropName {
                                                    span: span,
                                                    expr: sr(cx, c)?,
                                                })
                                            }
                                            _ => todo!(),
                                        },
                                        value: Box::new(Pat::Ident(any().into())),
                                    }))
                                })
                                .chain([Ok(ObjectPatProp::Rest(RestPat {
                                    span,
                                    dot3_token: span,
                                    arg: Box::new(Pat::Ident(rest.clone().into())),
                                    type_ann: None,
                                }))])
                                .collect::<Result<_, E>>()?,
                        })]
                        .into_iter()
                        .collect(),
                        body: Box::new(swc_ecma_ast::BlockStmtOrExpr::Expr(rest.into())),
                        is_async: false,
                        is_generator: false,
                        type_params: None,
                        return_type: None,
                    }))),
                    args: [ExprOrSpread {
                        expr: sr(cx, wrapped)?,
                        spread: None,
                    }]
                    .into_iter()
                    .collect(),
                    type_args: None,
                })
            }
            _ => todo!(), // Item::Intrinsic { value } => {
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
        return Ok(right);
    }
}
impl<I, F> Render<I, F> for LId<I> {
    type Result = AssignTarget;
    fn render<Cx, E>(
        &self,
        mark: &mut bool,
        span: Span,
        cx: &mut Cx,
        sr: &mut (dyn FnMut(&mut Cx, &I) -> Result<Box<Expr>, E> + '_),
        si: &mut (dyn FnMut(&mut Cx, &I) -> Result<swc_ecma_ast::Ident, E> + '_),
        sf: &mut (dyn FnMut(&mut Cx, &F) -> Result<Function, E> + '_),
    ) -> Result<Self::Result, E> {
        Ok(match self {
            crate::LId::Id { id } => swc_ecma_ast::AssignTarget::Simple(
                swc_ecma_ast::SimpleAssignTarget::Ident(swc_ecma_ast::BindingIdent {
                    id: si(cx, id)?,
                    type_ann: None,
                }),
            ),
            crate::LId::Member { obj, mem } => {
                *mark = true;
                // let obj = ident(obj, span);
                // let mem = ident(&mem[0], span);
                AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Member(MemberExpr {
                    span: span,
                    obj: sr(cx, obj)?,
                    prop: swc_ecma_ast::MemberProp::Computed(swc_ecma_ast::ComputedPropName {
                        span: span,
                        expr: sr(cx, &mem[0])?,
                    }),
                }))
            }
            LId::Private { obj, id } => {
                AssignTarget::Simple(swc_ecma_ast::SimpleAssignTarget::Member(MemberExpr {
                    span: span,
                    obj: sr(cx, obj)?,
                    prop: swc_ecma_ast::MemberProp::PrivateName(PrivateName {
                        span: id.span,
                        name: id.sym.clone(),
                    }),
                }))
            }
            // LId::SplitOff { head, tail } => {
            //     AssignTarget::Pat(swc_ecma_ast::AssignTargetPat::Array(ArrayPat {
            //         span,
            //         elems: [
            //             Some(Pat::Rest(RestPat {
            //                 span,
            //                 dot3_token: span,
            //                 arg: ident(head, span).into(),
            //                 type_ann: None,
            //             })),
            //             Some(ident(tail, span).into()),
            //         ]
            //         .into_iter()
            //         .collect(),
            //         optional: false,
            //         type_ann: None,
            //     }))
            // }
            _ => todo!(),
        })
    }
}
// #[derive(Default)]
#[non_exhaustive]
pub struct Rew<'a> {
    pub all: BTreeMap<TBlockId, swc_cfg::BlockId>,
    pub options: &'a Options<'a>,
}
impl Rew<'_> {
    pub fn trans(
        &mut self,
        cfg: &mut Cfg,
        tcfg: &TCfg,
        block_id: TBlockId,
    ) -> anyhow::Result<swc_cfg::BlockId> {
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
                        Some(Item::Asm { value })
                            if match value {
                                Asm::OrZero(value) => {
                                    tcfg.def(LId::Id { id: value.clone() }).is_some()
                                }
                                _ => todo!(),
                            } =>
                        {
                            match value {
                                Asm::OrZero(a) => Box::new(Expr::Bin(BinExpr {
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
                            }
                        }
                        Some(Item::Lit { lit }) => Box::new(Expr::Lit(lit.clone())),
                        Some(Item::Un { arg, op })
                            if !matches!(op, UnaryOp::Delete)
                                && tcfg.def(LId::Id { id: arg.clone() }).is_some() =>
                        {
                            Box::new(Expr::Unary(UnaryExpr {
                                span,
                                op: *op,
                                arg: _sr(arg, tcfg, state, span),
                            }))
                        }
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
                let left = statement_data.left.render(
                    &mut mark,
                    span,
                    &mut (),
                    &mut |_, a| Ok(sr(a)),
                    &mut |_, a| Ok(ident(a, span)),
                    &mut |_, f: &TFunc| {
                        f.to_func_with_options(self.options)
                            .and_then(|a| (self.options.conf)(a))
                    },
                )?;
                let right = statement_data.right.render(
                    &mut mark,
                    span,
                    &mut (),
                    &mut |_, a| Ok(sr(a)),
                    &mut |_, a| Ok(ident(a, span)),
                    &mut |_, f| {
                        f.to_func_with_options(self.options)
                            .and_then(|a| (self.options.conf)(a))
                    },
                )?;
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
                                    &a.0,
                                    tcfg.blocks[block_id]
                                        .post
                                        .orig_span
                                        .clone()
                                        .unwrap_or(Span::dummy_with_cmt()),
                                )),
                                self.trans(cfg, tcfg, a.1)?,
                            ))
                        })
                        .collect::<anyhow::Result<_>>()?,
                    default: self.trans(cfg, tcfg, *default)?,
                },
                crate::TTerm::Default => Term::Default,
                crate::TTerm::Tail { callee, args } => Term::Return(Some({
                    let i = Item::Call {
                        callee: callee.clone(),
                        args: args.clone(),
                    };
                    let span = tcfg.blocks[block_id]
                        .post
                        .orig_span
                        .clone()
                        .unwrap_or(Span::dummy_with_cmt());
                    let mut mark = false;
                    *i.render(
                        &mut mark,
                        span,
                        &mut (),
                        &mut |_, a| Ok(ident(a, span).into()),
                        &mut |_, a| Ok(ident(a, span)),
                        &mut |_, f: &TFunc| {
                            f.to_func_with_options(self.options)
                                .and_then(|a| (self.options.conf)(a))
                        },
                    )?
                })),
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
