//! Control Flow Graph (CFG) representation for JavaScript.
//!
//! This crate provides a CFG representation of JavaScript code, serving as an
//! intermediate layer between the Abstract Syntax Tree (AST) and lower-level
//! intermediate representations like TAC and SSA.
//!
//! # Control Flow Graph
//!
//! A CFG represents a program as a directed graph where:
//! - Nodes are basic blocks of sequential statements
//! - Edges represent possible control flow paths
//! - Each block has one entry point and one exit point (terminator)
//!
//! # Key Types
//!
//! - [`Func`]: A function represented as a CFG
//! - [`Cfg`]: The control flow graph structure
//! - [`Block`]: A basic block containing statements
//! - [`Term`]: A terminator (return, jump, branch, etc.)
//! - [`Catch`]: Exception handler specification
//!
//! # Conversion
//!
//! This crate converts SWC's JavaScript AST into CFG form, handling:
//! - Loops (for, while, do-while)
//! - Conditionals (if-else, switch)
//! - Exception handling (try-catch-finally)
//! - Labels and break/continue statements
//!
//! # Modules
//!
//! - [`recfg`]: CFG restructuring and transformation
//! - [`simplify`]: CFG simplification passes
//! - [`to_cfg`]: Conversion from AST to CFG

use anyhow::Context;
use id_arena::{Arena, Id};
use relooper::ShapedBlock;
use std::{collections::HashMap, iter::once};
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
/// A function represented as a control flow graph.
///
/// This is the CFG representation of a JavaScript/TypeScript function, including
/// its parameters, control flow structure, and metadata.
///
/// # Fields
///
/// - `cfg`: The control flow graph containing all basic blocks
/// - `entry`: The entry block where execution begins
/// - `params`: Function parameters (as SWC AST `Param` nodes)
/// - `is_generator`: Whether this is a generator function
/// - `is_async`: Whether this is an async function
#[derive(Clone)]
pub struct Func {
    /// The control flow graph
    pub cfg: Cfg,
    /// The entry block identifier
    pub entry: Id<Block>,
    /// Function parameters
    pub params: Vec<Param>,
    /// Whether this is a generator function (function*)
    pub is_generator: bool,
    /// Whether this is an async function
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
            None,
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
/// A control flow graph containing basic blocks.
///
/// The CFG is the core data structure representing a function's control flow.
/// It contains an arena of blocks that are connected through their terminators.
///
/// # Fields
///
/// - `blocks`: Arena of all basic blocks in the CFG
/// - `generics`: Optional generic type parameters (for TypeScript)
/// - `ts_retty`: Optional return type annotation (for TypeScript)
#[derive(Clone, Default)]
pub struct Cfg {
    /// Arena containing all basic blocks
    pub blocks: Arena<Block>,
    /// Generic type parameters (TypeScript)
    pub generics: Option<TsTypeParamDecl>,
    /// Return type annotation (TypeScript)
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
                                value: Atom::new(k.index().to_string()).into(),
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
                                                        value: Atom::new(l.index().to_string()).into(),
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
/// A basic block in the control flow graph.
///
/// A basic block contains a sequence of statements with no internal control flow,
/// followed by a terminator that specifies how control exits the block.
///
/// # Fields
///
/// - `stmts`: Sequential statements in this block (as SWC AST `Stmt` nodes)
/// - `end`: The block's terminator and exception handler
#[derive(Default, Clone)]
pub struct Block {
    /// Statements executed sequentially in this block
    pub stmts: Vec<Stmt>,
    /// Terminator and exception handler
    pub end: End,
}

/// The end (exit point) of a basic block.
///
/// Similar to TAC's `TPostecedent` and SSA's `SPostcedent`, this specifies
/// both normal control flow (terminator) and exception handling.
///
/// # Fields
///
/// - `catch`: Exception handler specification
/// - `term`: Normal control flow terminator
/// - `orig_span`: Original source location
#[derive(Default, Clone)]
pub struct End {
    /// Exception handler
    pub catch: Catch,
    /// Normal control flow terminator
    pub term: Term,
    /// Original source span for debugging
    pub orig_span: Option<Span>,
}
/// Exception handler specification for CFG blocks.
///
/// Specifies what happens when an exception is thrown during block execution.
/// Similar to TAC's `TCatch` but uses SWC AST types.
#[derive(Clone, Default)]
pub enum Catch {
    /// No exception handler - propagate to caller
    #[default]
    Throw,
    /// Jump to catch handler, binding exception to pattern
    Jump {
        /// Pattern to bind the exception value to
        pat: Pat,
        /// The catch handler block
        k: Id<Block>,
    },
}

/// A block terminator specifying control flow.
///
/// Each basic block ends with exactly one terminator that determines where
/// control flow goes next. This is similar to TAC's `TTerm` but uses SWC AST
/// expression nodes for values.
#[derive(Default, Clone)]
pub enum Term {
    /// Return from function, optionally with a value
    Return(Option<Expr>),
    /// Throw an exception with the given expression
    Throw(Expr),
    /// Unconditional jump to another block
    Jmp(Id<Block>),
    /// Conditional jump based on a boolean expression
    CondJmp {
        /// The condition expression
        cond: Expr,
        /// Block to jump to if condition is truthy
        if_true: Id<Block>,
        /// Block to jump to if condition is falsy
        if_false: Id<Block>,
    },
    /// Multi-way branch (switch statement)
    Switch {
        /// The expression being switched on
        x: Expr,
        /// Map from case values to target blocks
        blocks: HashMap<Expr, Id<Block>>,
        /// Default block if no case matches
        default: Id<Block>,
    },
    /// Placeholder or unreachable terminator
    #[default]
    Default,
}
pub mod to_cfg;
