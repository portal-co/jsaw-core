use std::{collections::HashMap, iter::once};

use anyhow::Context;
use id_arena::{Arena, Id};
use relooper::ShapedBlock;
use swc_atoms::Atom;
use swc_common::{Span, Spanned, SyntaxContext};
use swc_ecma_ast::{
    ArrayLit, AssignExpr, BindingIdent, BlockStmt, Bool, BreakStmt, CallExpr, CatchClause,
    ContinueStmt, Decl, DoWhileStmt, Expr, ExprOrSpread, ExprStmt, ForStmt, Function, Ident,
    IdentName, IfStmt, LabeledStmt, Lit, MemberExpr, Param, Pat, ReturnStmt, Stmt, Str, SwitchCase,
    SwitchStmt, ThrowStmt, TryStmt, TsTypeAnn, TsTypeParamDecl, WhileStmt,
};
pub mod recfg;
pub mod simplify;
#[derive(Clone)]
pub struct Func {
    pub cfg: Cfg,
    pub entry: Id<Block>,
    pub params: Vec<Param>,
    pub is_generator: bool,
    pub is_async: bool,
}
impl Default for Func {
    fn default() -> Self {
        let mut cfg = Cfg::default();
        let entry = cfg.blocks.alloc(Default::default());
        Self {
            cfg,
            entry,
            params: Default::default(),
            is_generator: Default::default(),
            is_async: Default::default(),
        }
    }
}
impl TryFrom<Function> for Func {
    type Error = anyhow::Error;

    fn try_from(value: Function) -> Result<Self, Self::Error> {
        let mut cfg = Cfg::default();
        let entry = cfg.blocks.alloc(Default::default());
        let exit = to_cfg::ToCfgConversionCtx::default().transform_all(
            &mut cfg,
            &value.body.map(|a| a.stmts).unwrap_or_else(Vec::new),
            entry,
        )?;
        cfg.blocks[exit].end.term = Term::Return(None);
        cfg.simplify();
        cfg.generics = value.type_params.map(|a| *a);
        cfg.ts_retty = value.return_type.map(|a| *a);
        return Ok(Self {
            cfg,
            entry,
            params: value.params,
            is_generator: value.is_generator,
            is_async: value.is_async,
        });
    }
}
impl Into<Function> for Func {
    fn into(self) -> Function {
        let k = ssa_reloop::go(&self, self.entry);
        let stmts = Cfg::process_block(&self.cfg, &k, Span::dummy_with_cmt(), Default::default());
        return Function {
            params: self.params,
            decorators: vec![],
            span: Span::dummy_with_cmt(),
            ctxt: Default::default(),
            body: Some(BlockStmt {
                span: Span::dummy_with_cmt(),
                ctxt: Default::default(),
                stmts,
            }),
            is_generator: self.is_generator,
            is_async: self.is_async,
            type_params: self.cfg.generics.map(Box::new),
            return_type: self.cfg.ts_retty.map(Box::new),
        };
    }
}

#[derive(Clone, Default)]
pub struct Cfg {
    pub blocks: Arena<Block>,
    pub generics: Option<TsTypeParamDecl>,
    pub ts_retty: Option<TsTypeAnn>,
}
impl Cfg {
    pub fn recfg(&self, entry: Id<Block>) -> (Cfg, Id<Block>) {
        let mut res = Cfg::default();
        res.generics = self.generics.clone();
        res.ts_retty = self.ts_retty.clone();
        let Ok(entry) = recfg::Recfg::default().go(self, &mut res, entry) else {
            return (self.clone(), entry);
        };
        return (res, entry);
    }
    // pub fn reloop_block(&self, entry: Id<Block>) -> ShapedBlock<Id<Block>> {
    //     return *relooper::reloop(
    //         self.blocks
    //             .iter()
    //             .map(|(a, k)| {
    //                 (
    //                     a,
    //                     match &k.end.catch {
    //                         Catch::Throw => None,
    //                         Catch::Jump { pat, k } => Some(*k),
    //                     }
    //                     .into_iter()
    //                     .chain(
    //                         match &k.end.term {
    //                             Term::Return(expr) => vec![],
    //                             Term::Throw(expr) => vec![],
    //                             Term::Jmp(id) => vec![*id],
    //                             Term::CondJmp {
    //                                 cond,
    //                                 if_true,
    //                                 if_false,
    //                             } => vec![*if_true, *if_false],
    //                             Term::Switch { x, blocks, default } => {
    //                                 blocks.values().cloned().chain(once(*default)).collect()
    //                             }
    //                             Term::Default => vec![],
    //                         }
    //                         .into_iter(),
    //                     )
    //                     .collect::<BTreeSet<_>>()
    //                     .into_iter()
    //                     .collect(),
    //                 )
    //             })
    //             .collect(),
    //         entry,
    //     );
    // }
    pub fn process_block(
        &self,
        k: &ShapedBlock<Id<Block>>,
        span: Span,
        ctxt: SyntaxContext,
    ) -> Vec<Stmt> {
        match k {
            ShapedBlock::Simple(simple_block) => {
                let span = match self.blocks[simple_block.label].end.orig_span.clone() {
                    None => span,
                    Some(s) => s,
                };
                let jmp = |k: Id<Block>| {
                    vec![Stmt::Expr(ExprStmt {
                        span,
                        expr: Box::new(Expr::Assign(AssignExpr {
                            span,
                            op: swc_ecma_ast::AssignOp::Assign,
                            left: Ident::new(Atom::new("cff"), span, ctxt).into(),
                            right: Box::new(Expr::Lit(Lit::Str(Str {
                                span,
                                value: Atom::new(k.index().to_string()),
                                raw: None,
                            }))),
                        })),
                    })]
                    .into_iter()
                    .chain(
                        match simple_block.branches.get(&k) {
                            None => vec![],
                            Some(a) => match a {
                                relooper::BranchMode::LoopBreak(l)
                                | relooper::BranchMode::LoopBreakIntoMulti(l) => {
                                    vec![Stmt::Break(BreakStmt {
                                        span,
                                        label: Some(Ident::new(
                                            Atom::new(format!("${l}")),
                                            span,
                                            ctxt,
                                        )),
                                    })]
                                }
                                relooper::BranchMode::LoopContinue(l)
                                | relooper::BranchMode::LoopContinueIntoMulti(l) => {
                                    vec![Stmt::Continue(ContinueStmt {
                                        span,
                                        label: Some(Ident::new(
                                            Atom::new(format!("${l}")),
                                            span,
                                            ctxt,
                                        )),
                                    })]
                                }
                                relooper::BranchMode::MergedBranch => vec![],
                                relooper::BranchMode::MergedBranchIntoMulti => vec![],
                                relooper::BranchMode::SetLabelAndBreak => {
                                    vec![Stmt::Break(BreakStmt { span, label: None })]
                                }
                            },
                        }
                        .into_iter(),
                    )
                    .collect::<Vec<_>>()
                };
                let l = simple_block.label;
                let body = self.blocks[l].stmts.iter().cloned().collect::<Vec<_>>();
                let mut body = match &self.blocks[l].end.catch {
                    Catch::Throw => body,
                    Catch::Jump { pat, k } => {
                        let id = Ident::new_private(Atom::new("caught"), span);
                        vec![Stmt::Try(Box::new(TryStmt {
                            span,
                            block: BlockStmt {
                                span,
                                ctxt,
                                stmts: body,
                            },
                            finalizer: None,
                            handler: Some(CatchClause {
                                span,
                                param: Some(Pat::Ident(id.clone().into())),
                                body: BlockStmt {
                                    span,
                                    ctxt,
                                    stmts: vec![Stmt::Expr(ExprStmt {
                                        span,
                                        expr: Box::new(Expr::Assign(AssignExpr {
                                            span,
                                            op: swc_ecma_ast::AssignOp::Assign,
                                            left: pat.clone().try_into().unwrap(),
                                            right: Box::new(Expr::Ident(id)),
                                        })),
                                    })]
                                    .into_iter()
                                    .chain(jmp(*k).into_iter())
                                    .collect(),
                                },
                            }),
                        }))]
                    }
                };
                match &self.blocks[l].end.term {
                    Term::Return(expr) => body.push(Stmt::Return(ReturnStmt {
                        span,
                        arg: expr.as_ref().cloned().map(Box::new),
                    })),
                    Term::Throw(expr) => body.push(Stmt::Throw(ThrowStmt {
                        span,
                        arg: Box::new(expr.clone()),
                    })),
                    Term::Jmp(id) => body.extend(jmp(*id).into_iter()),
                    Term::CondJmp {
                        cond,
                        if_true,
                        if_false,
                    } => body.push(Stmt::If(IfStmt {
                        span,
                        test: Box::new(cond.clone()),
                        cons: Box::new(Stmt::Block(BlockStmt {
                            span,
                            ctxt,
                            stmts: jmp(*if_true),
                        })),
                        alt: Some(Box::new(Stmt::Block(BlockStmt {
                            span,
                            ctxt,
                            stmts: jmp(*if_false),
                        }))),
                    })),
                    Term::Switch { x, blocks, default } => {
                        body.push(Stmt::Switch(SwitchStmt {
                            span,
                            discriminant: Box::new(x.clone()),
                            cases: blocks
                                .iter()
                                .map(|(i, k)| SwitchCase {
                                    span,
                                    test: Some(Box::new(i.clone())),
                                    cons: jmp(*k),
                                })
                                .chain(once(SwitchCase {
                                    span,
                                    test: None,
                                    cons: jmp(*default),
                                }))
                                .collect(),
                        }));
                    }
                    Term::Default => {}
                };
                for x in [simple_block.immediate.as_ref(), simple_block.next.as_ref()] {
                    body.extend(
                        x.into_iter()
                            .flat_map(|i| self.process_block(i.as_ref(), span, ctxt)),
                    );
                }
                return body;
            }
            ShapedBlock::Loop(loop_block) => once(Stmt::Labeled(LabeledStmt {
                span,
                label: Ident::new(Atom::new(format!("${}", loop_block.loop_id)), span, ctxt),
                body: Box::new(Stmt::For(ForStmt {
                    span,
                    init: None,
                    test: None,
                    update: None,
                    body: Box::new(Stmt::Block(BlockStmt {
                        span,
                        ctxt,
                        stmts: self.process_block(&*loop_block.inner, span, ctxt),
                    })),
                })),
            }))
            .chain(
                loop_block
                    .next
                    .as_ref()
                    .into_iter()
                    .flat_map(|a| self.process_block(&*a, span, ctxt).into_iter()),
            )
            .collect(),
            ShapedBlock::Multiple(multiple_block) => vec![Stmt::Switch(SwitchStmt {
                span,
                discriminant: Box::new(Expr::Lit(Lit::Bool(Bool { span, value: true }))),
                cases: multiple_block
                    .handled
                    .iter()
                    .map(|h| SwitchCase {
                        span,
                        test: Some(Box::new(Expr::Call(CallExpr {
                            span,
                            ctxt,
                            callee: swc_ecma_ast::Callee::Expr(Box::new(
                                MemberExpr {
                                    span,
                                    obj: Box::new(Expr::Array(ArrayLit {
                                        span,
                                        elems: h
                                            .labels
                                            .iter()
                                            .map(|l| {
                                                Some(ExprOrSpread {
                                                    spread: None,
                                                    expr: Box::new(Expr::Lit(Lit::Str(Str {
                                                        span,
                                                        value: Atom::new(l.index().to_string()),
                                                        raw: None,
                                                    }))),
                                                })
                                            })
                                            .collect(),
                                    })),
                                    prop: swc_ecma_ast::MemberProp::Ident(IdentName {
                                        span,
                                        sym: Atom::new("contains"),
                                    }),
                                }
                                .into(),
                            )),
                            args: vec![ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident::new(
                                    Atom::new("cff"),
                                    span,
                                    ctxt,
                                ))),
                            }],
                            type_args: None,
                        }))),
                        cons: self
                            .process_block(&h.inner, span, ctxt)
                            .into_iter()
                            .chain(
                                if h.break_after {
                                    Some(Stmt::Break(swc_ecma_ast::BreakStmt { span, label: None }))
                                } else {
                                    None
                                }
                                .into_iter(),
                            )
                            .collect(),
                    })
                    .collect(),
            })],
        }
    }
}

impl cfg_traits::Func for Func {
    type Block = Id<Block>;

    type Blocks = Arena<Block>;

    fn blocks(&self) -> &Self::Blocks {
        &self.cfg.blocks
    }

    fn blocks_mut(&mut self) -> &mut Self::Blocks {
        &mut self.cfg.blocks
    }

    fn entry(&self) -> Self::Block {
        self.entry
    }
}

impl cfg_traits::Block<Func> for Block {
    type Terminator = End;

    fn term(&self) -> &Self::Terminator {
        &self.end
    }

    fn term_mut(&mut self) -> &mut Self::Terminator {
        &mut self.end
    }
}

impl cfg_traits::Term<Func> for End {
    type Target = Id<Block>;

    fn targets<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::Target> + 'a>
    where
        Func: 'a,
    {
        Box::new(
            match &self.catch {
                Catch::Throw => None,
                Catch::Jump { pat, k } => Some(k),
            }
            .into_iter()
            .chain(
                match &self.term {
                    Term::Return(expr) => vec![],
                    Term::Throw(expr) => vec![],
                    Term::Jmp(id) => vec![id],
                    Term::CondJmp {
                        cond,
                        if_true,
                        if_false,
                    } => vec![if_true, if_false],
                    Term::Switch { x, blocks, default } => {
                        blocks.values().chain(once(default)).collect()
                    }
                    Term::Default => vec![],
                }
                .into_iter(),
            ),
        )
    }

    fn targets_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Self::Target> + 'a>
    where
        Func: 'a,
    {
        Box::new(
            match &mut self.catch {
                Catch::Throw => None,
                Catch::Jump { pat, k } => Some(k),
            }
            .into_iter()
            .chain(
                match &mut self.term {
                    Term::Return(expr) => vec![],
                    Term::Throw(expr) => vec![],
                    Term::Jmp(id) => vec![id],
                    Term::CondJmp {
                        cond,
                        if_true,
                        if_false,
                    } => vec![if_true, if_false],
                    Term::Switch { x, blocks, default } => {
                        blocks.values_mut().chain(once(default)).collect()
                    }
                    Term::Default => vec![],
                }
                .into_iter(),
            ),
        )
    }
}

impl cfg_traits::Term<Func> for Id<Block> {
    type Target = Id<Block>;

    fn targets<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::Target> + 'a>
    where
        Func: 'a,
    {
        Box::new(once(self))
    }

    fn targets_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Self::Target> + 'a>
    where
        Func: 'a,
    {
        Box::new(once(self))
    }
}

impl cfg_traits::Target<Func> for Id<Block> {
    fn block(&self) -> <Func as cfg_traits::Func>::Block {
        *self
    }

    fn block_mut(&mut self) -> &mut <Func as cfg_traits::Func>::Block {
        self
    }
}

#[derive(Default, Clone)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub end: End,
}
#[derive(Default, Clone)]
pub struct End {
    pub catch: Catch,
    pub term: Term,
    pub orig_span: Option<Span>,
}
#[derive(Clone, Default)]
pub enum Catch {
    #[default]
    Throw,
    Jump {
        pat: Pat,
        k: Id<Block>,
    },
}
#[derive(Default, Clone)]
pub enum Term {
    Return(Option<Expr>),
    Throw(Expr),
    Jmp(Id<Block>),
    CondJmp {
        cond: Expr,
        if_true: Id<Block>,
        if_false: Id<Block>,
    },
    Switch {
        x: Expr,
        blocks: HashMap<Expr, Id<Block>>,
        default: Id<Block>,
    },
    #[default]
    Default,
}
pub mod to_cfg;