//! Preparation passes for JavaScript before TAC conversion.
//!
//! This module contains preprocessing transformations that prepare JavaScript
//! code for conversion to TAC. These passes:
//! - Simplify complex expressions
//! - Normalize syntax
//! - Hoist declarations
//! - Handle proxy detection for optimization
//!
//! # Key Type
//!
//! [`Prepa`] - The main preparation visitor that transforms JavaScript AST

use super::*;
use portal_solutions_proxy_signs::PROXY_SIGNS;
use std::{
    mem::replace,
    sync::{OnceLock, atomic::AtomicUsize},
};
use swc_ecma_ast::{
    AssignExpr, BinExpr, CallExpr, CondExpr, Decl, ExprOrSpread, ExprStmt, IdentName, ModuleItem,
    PrivateName, SeqExpr, ThisExpr, VarDecl, VarDeclarator,
};
use swc_ecma_visit::{VisitMut, VisitMutWith};

/// Preparation visitor for preprocessing JavaScript AST.
///
/// This visitor performs normalization and simplification passes on the
/// JavaScript AST before it's converted to TAC, making the conversion
/// process simpler and more reliable.
///
/// # Fields
///
/// - `semantics`: Semantic configuration
/// - `resolver`: Atom resolver for generating fresh names
/// - `vars`: Set of declared variables
/// - `idx`: Counter for generating unique names
/// - `ctxt`: Syntax context for generated identifiers
#[non_exhaustive]
pub struct Prepa<'a> {
    /// Semantic configuration
    pub semantics: &'a SemanticCfg,
    /// Resolver for generating fresh variable names
    pub resolver: Arc<dyn AtomResolver>,
    /// Set of variables encountered
    vars: BTreeSet<Ident>,
    /// Counter for unique name generation
    idx: AtomicUsize,
    /// Syntax context for generated identifiers
    ctxt: OnceLock<SyntaxContext>,
}
impl<'a> Prepa<'a> {
    pub fn new(semantics: &'a SemanticCfg, resolver: Arc<dyn AtomResolver>) -> Self {
        Self {
            semantics,
            vars: Default::default(),
            resolver,
            idx: Default::default(),
            ctxt: Default::default(),
        }
    }
    fn pull(&self) -> Ident {
        (
            self.resolver
                .resolve(self.idx.fetch_add(1, std::sync::atomic::Ordering::SeqCst)),
            *self
                .ctxt
                .get_or_init(|| SyntaxContext::empty().apply_mark(Mark::new())),
        )
    }
}
fn eq(mut left: &Expr, mut right: &Expr) -> bool {
    loop {
        return match (left, right) {
            (Expr::Ident(i), Expr::Ident(j)) => i.to_id() == j.to_id(),
            (Expr::Assign(a), b) => {
                left = &a.right;
                continue;
            }
            (b, Expr::Assign(a)) => {
                right = &a.right;
                continue;
            }
            _ => false,
        };
    }
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
    fn visit_mut_seq_expr(&mut self, node: &mut SeqExpr) {
        let mut again = true;
        while take(&mut again) {
            node.visit_mut_children_with(self);
            node.exprs = node
                .exprs
                .drain(..)
                .flat_map(|a| match *a {
                    Expr::Seq(SeqExpr { span, exprs }) => {
                        again = true;
                        exprs
                    }
                    a => [Box::new(a)].into_iter().collect::<Vec<_>>(),
                })
                .collect();
            let l = node.exprs.len();
            for (i, e) in take(&mut node.exprs).into_iter().enumerate() {
                if let Some(i) = node
                    .exprs
                    .last()
                    .and_then(|a| a.as_assign())
                    .and_then(|a| a.left.as_ident())
                    && let Some(j) = e.as_ident()
                {
                    if i.to_id() == j.to_id() {
                        again = true;
                        continue;
                    }
                }
                if i + 1 == l {
                } else {
                    if e.is_lit() || e.is_ident() {
                        again = true;
                        continue;
                    }
                }
                node.exprs.push(e);
            }
        }
    }
    fn visit_mut_expr(&mut self, node: &mut Expr) {
        let mut again = true;
        while take(&mut again) {
            node.visit_mut_children_with(self);
            *node = match take(node) {
                Expr::Seq(SeqExpr { span, mut exprs }) if exprs.len() == 1 => {
                    again = true;
                    *exprs.remove(0)
                }
                Expr::Bin(BinExpr {
                    span,
                    op,
                    left,
                    right,
                }) => match op {
                    BinaryOp::LogicalOr => {
                        again = true;
                        let lhs = self.pull();
                        self.vars.insert(lhs.clone());
                        Expr::Cond(CondExpr {
                            span,
                            test: Box::new(Expr::Assign(AssignExpr {
                                span,
                                op: AssignOp::Assign,
                                left: AssignTarget::Simple(SimpleAssignTarget::Ident(
                                    lhs.clone().into(),
                                )),
                                right: left,
                            })),
                            cons: lhs.into(),
                            alt: right,
                        })
                    }
                    BinaryOp::LogicalAnd => {
                        again = true;
                        let lhs = self.pull();
                        self.vars.insert(lhs.clone());
                        Expr::Cond(CondExpr {
                            span,
                            test: Box::new(Expr::Assign(AssignExpr {
                                span,
                                op: AssignOp::Assign,
                                left: AssignTarget::Simple(SimpleAssignTarget::Ident(
                                    lhs.clone().into(),
                                )),
                                right: left,
                            })),
                            cons: right,
                            alt: lhs.into(),
                        })
                    }
                    BinaryOp::NullishCoalescing => {
                        let lhs = self.pull();
                        self.vars.insert(lhs.clone());
                        Expr::Cond(CondExpr {
                            span,
                            test: Box::new(Expr::Bin(BinExpr {
                                span,
                                op: BinaryOp::EqEqEq,
                                left: Box::new(Expr::Assign(AssignExpr {
                                    span,
                                    op: AssignOp::Assign,
                                    left: AssignTarget::Simple(SimpleAssignTarget::Ident(
                                        lhs.clone().into(),
                                    )),
                                    right: left,
                                })),
                                right: Expr::undefined(span),
                            })),
                            cons: right,
                            alt: lhs.into(),
                        })
                    }
                    _ => Expr::Bin(BinExpr {
                        span,
                        op,
                        left,
                        right,
                    }),
                },
                node => node,
            };
            // let vp = |e: &Expr| match e {
            //     Expr::Ident(i) => {
            //         i.ctxt == Default::default()
            //             && ["pan_eval", "$scramjet", "__uv", "__PortalEnterprise"]
            //                 .contains(&i.sym.as_str())
            //     }
            //     _ => false,
            // };
            if self
                .semantics
                .flags
                .contains(SemanticFlags::BITWISE_OR_ABSENT_NAN)
            {
                *node = match take(node) {
                    Expr::Bin(BinExpr {
                        span,
                        op,
                        left,
                        right,
                    }) => match op {
                        BinaryOp::EqEqEq | BinaryOp::EqEq if eq(&left, &right) => {
                            again = true;
                            Expr::Seq(SeqExpr {
                                span,
                                exprs: [
                                    left,
                                    right,
                                    Box::new(Expr::Lit(Lit::Bool(Bool { span, value: true }))),
                                ]
                                .into_iter()
                                .collect(),
                            })
                        }
                        BinaryOp::NotEqEq | BinaryOp::NotEq if eq(&left, &right) => {
                            again = true;
                            Expr::Seq(SeqExpr {
                                span,
                                exprs: [
                                    left,
                                    right,
                                    Box::new(Expr::Lit(Lit::Bool(Bool { span, value: false }))),
                                ]
                                .into_iter()
                                .collect(),
                            })
                        }
                        op => Expr::Bin(BinExpr {
                            span,
                            op,
                            left,
                            right,
                        }),
                    },
                    node => node,
                }
            }
            portal_solutions_swibb::folding::CondFolding::default().visit_mut_expr(node);
        }
    }
}
