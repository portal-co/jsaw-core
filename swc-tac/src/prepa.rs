use std::mem::replace;

use swc_ecma_ast::{
    AssignExpr, BinExpr, CondExpr, Decl, ExprStmt, ModuleItem, PrivateName, SeqExpr, ThisExpr,
    VarDecl, VarDeclarator,
};
use swc_ecma_visit::{VisitMut, VisitMutWith};

use super::*;
#[non_exhaustive]
pub struct Prepa<'a> {
    pub semantics: &'a SemanticCfg,
    vars: BTreeSet<Ident>,
}
impl VisitMut for Prepa<'_> {
    fn visit_mut_stmts(&mut self, node: &mut Vec<Stmt>) {
        let vars = take(&mut self.vars);
        node.visit_mut_children_with(self);
        let vars = replace(&mut self.vars, vars);
        node.insert(
            0,
            Stmt::Decl(Decl::Var(Box::new(VarDecl {
                span: Span::dummy_with_cmt(),
                ctxt: Default::default(),
                kind: swc_ecma_ast::VarDeclKind::Let,
                declare: false,
                decls: vars
                    .into_iter()
                    .map(|a| VarDeclarator {
                        span: Span::dummy_with_cmt(),
                        name: Pat::Ident(a.into()),
                        init: None,
                        definite: false,
                    })
                    .collect(),
            }))),
        );
    }
    fn visit_mut_module(&mut self, node: &mut swc_ecma_ast::Module) {
        let vars = take(&mut self.vars);
        node.visit_mut_children_with(self);
        let vars = replace(&mut self.vars, vars);
        node.body.insert(
            0,
            ModuleItem::Stmt(Stmt::Decl(Decl::Var(Box::new(VarDecl {
                span: Span::dummy_with_cmt(),
                ctxt: Default::default(),
                kind: swc_ecma_ast::VarDeclKind::Let,
                declare: false,
                decls: vars
                    .into_iter()
                    .map(|a| VarDeclarator {
                        span: Span::dummy_with_cmt(),
                        name: Pat::Ident(a.into()),
                        init: None,
                        definite: false,
                    })
                    .collect(),
            })))),
        );
    }
    fn visit_mut_class(&mut self, node: &mut Class) {
        node.visit_mut_children_with(self);
        let span = node.span;
        #[derive(PartialEq, Eq, Hash)]
        enum Prop {
            Key(swc_ecma_ast::PropName),
            Private(PrivateName),
        }
        let mut m = HashMap::new();
        for i in node.body.iter_mut() {
            match i {
                ClassMember::ClassProp(c) => {
                    if !c.is_static {
                        if let Some(i) = c.value.take() {
                            m.insert(Prop::Key(c.key.clone()), i);
                        }
                    }
                }
                ClassMember::PrivateProp(c) => {
                    if !c.is_static {
                        if let Some(i) = c.value.take() {
                            m.insert(Prop::Private(c.key.clone()), i);
                        }
                    }
                }
                _ => {}
            }
        }
        let needs_super = node.super_class.is_some();
        for i in node.body.iter_mut().filter_map(|a| a.as_mut_constructor()) {
            if !needs_super {
                for _ in i.body.get_or_insert_default().stmts.splice(
                    0..0,
                    take(&mut m).into_iter().map(|(a, b)| {
                        Stmt::Expr(ExprStmt {
                            span,
                            expr: Box::new(Expr::Assign(AssignExpr {
                                span,
                                op: swc_ecma_ast::AssignOp::Assign,
                                right: b,
                                left: swc_ecma_ast::AssignTarget::Simple(
                                    SimpleAssignTarget::Member(MemberExpr {
                                        span,
                                        obj: Box::new(Expr::This(ThisExpr { span })),
                                        prop: match a {
                                            Prop::Key(prop_name) => prop_name.into(),
                                            Prop::Private(private_name) => private_name.into(),
                                        },
                                    }),
                                ),
                            })),
                        })
                    }),
                ) {}
            } else {
                struct Traverse {
                    props: HashMap<Prop, Box<Expr>>,
                }
                impl VisitMut for Traverse {
                    fn visit_mut_class(&mut self, node: &mut Class) {}
                    fn visit_mut_expr(&mut self, node: &mut Expr) {
                        node.visit_mut_children_with(self);
                        if let Expr::Call(c) = node {
                            if let Callee::Super(s) = &c.callee {
                                let span = s.span;
                                let x = take(&mut self.props).into_iter().map(|(a, b)| {
                                    Box::new(Expr::Assign(AssignExpr {
                                        span,
                                        op: swc_ecma_ast::AssignOp::Assign,
                                        right: b,
                                        left: swc_ecma_ast::AssignTarget::Simple(
                                            SimpleAssignTarget::Member(MemberExpr {
                                                span,
                                                obj: Box::new(Expr::This(ThisExpr { span })),
                                                prop: match a {
                                                    Prop::Key(prop_name) => prop_name.into(),
                                                    Prop::Private(private_name) => {
                                                        private_name.into()
                                                    }
                                                },
                                            }),
                                        ),
                                    }))
                                });
                                *node = Expr::Seq(SeqExpr {
                                    span,
                                    exprs: [take(node)]
                                        .into_iter()
                                        .map(Box::new)
                                        .chain(x)
                                        .collect(),
                                })
                            }
                        }
                    }
                }
                i.visit_mut_children_with(&mut Traverse {
                    props: take(&mut m),
                });
            }
        }
    }
    fn visit_mut_expr(&mut self, node: &mut Expr) {
        node.visit_mut_children_with(self);
        if self
            .semantics
            .flags
            .contains(SemanticFlags::BITWISE_OR_ABSENT_NAN)
        {
            for a in [(Atom::new("globalThis"), SyntaxContext::empty())] {
                *node = match take(node) {
                    Expr::Member(m) => {
                        let b = (
                            Atom::new("$"),
                            SyntaxContext::empty().apply_mark(Mark::new()),
                        );
                        self.vars.insert(b.clone());
                        Expr::Cond(CondExpr {
                            span: m.span,
                            test: Box::new(Expr::Bin(BinExpr {
                                span: m.span,
                                op: BinaryOp::EqEqEq,
                                left: Box::new(Expr::Assign(AssignExpr {
                                    span: m.span,
                                    op: swc_ecma_ast::AssignOp::Assign,
                                    left: swc_ecma_ast::AssignTarget::Simple(
                                        SimpleAssignTarget::Ident(b.clone().into()),
                                    ),
                                    right: m.obj,
                                })),
                                right: a.clone().into(),
                            })),
                            cons: Box::new(Expr::Member(MemberExpr {
                                span: m.span,
                                obj: a.clone().into(),
                                prop: m.prop.clone(),
                            })),
                            alt: Box::new(Expr::Member(MemberExpr {
                                span: m.span,
                                obj: b.clone().into(),
                                prop: m.prop.clone(),
                            })),
                        })
                    }
                    node => node,
                }
            }
        }
    }
}
