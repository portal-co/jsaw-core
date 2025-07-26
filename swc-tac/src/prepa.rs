use swc_ecma_ast::{AssignExpr, ExprStmt, PrivateName, SeqExpr, ThisExpr};
use swc_ecma_visit::{VisitMut, VisitMutWith};

use super::*;
#[non_exhaustive]
pub struct Prepa<'a> {
    pub semantics: &'a SemanticCfg,
}
impl VisitMut for Prepa<'_> {
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
}
