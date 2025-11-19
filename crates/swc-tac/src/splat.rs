//! Function inlining transformation for TAC.
//!
//! This module performs function inlining, replacing function calls with the
//! function body when the callee is statically known. This optimization:
//! - Eliminates call overhead
//! - Enables further optimizations on the inlined code
//! - Handles argument binding and parameter passing
//! - Preserves `this` binding semantics for methods
//!
//! # Inlining Process
//!
//! The inlining transformation:
//! 1. Identifies calls to statically-known functions (direct calls or via constants)
//! 2. Binds call arguments to function parameters
//! 3. Inlines the function's CFG into the caller
//! 4. Handles return values by redirecting returns to the call site
//! 5. Manages `this` binding for arrow functions vs regular functions
//! 6. Supports `.call()` method inlining for explicit `this` binding
//!
//! # Suggested Name Changes
//!
//! This module should be renamed to better reflect its purpose:
//! - **Recommended**: `inline.rs` - clearly indicates function inlining
//! - **Alternative**: `inline_functions.rs` - more explicit
//! - Type `Splatting` → `Inliner` or `FunctionInliner`
//! - Method `splatted()` → `inlined()` or `with_inlining()`
//!
//! # Key Type
//!
//! [`Splatting`] - The inlining transformation state (should be renamed to `Inliner`)

use crate::*;
use portal_jsc_common::syntax::ThisArg;
use std::mem::replace;
use swc_ll_common::ext::Verbatim;
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

/// State for function inlining transformations.
///
/// Maintains context while inlining function calls into the caller's TAC.
/// Tracks block mappings, exception handlers, return targets, and recursion
/// prevention.
///
/// # Suggested Rename
///
/// This type should be renamed to `Inliner` or `FunctionInliner` to better
/// reflect its purpose.
///
/// # Fields
///
/// - `cache`: Mapping from input blocks to output blocks (for memoization)
/// - `catch`: Current exception handler context
/// - `ret`: Return target for the inlined function (left-hand side, continuation block, arguments object)
/// - `this_val`: The `this` binding for the inlined function
/// - `stack`: Set of function identifiers currently being inlined (prevents infinite recursion)
#[derive(Default)]
pub struct Splatting {
    /// Cache mapping input blocks to output blocks (for memoization)
    pub cache: BTreeMap<Id<TBlock>, Id<TBlock>>,
    /// Current exception handler context
    pub catch: TCatch,
    /// Return target for inlined function: (result variable, continuation block, arguments array)
    pub ret: Option<(LId, Id<TBlock>, Ident)>,
    /// The `this` binding for the inlined function
    pub this_val: Option<Ident>,
    /// Functions currently being inlined (prevents infinite recursion)
    pub stack: BTreeSet<Ident>,
}
impl Splatting {
    fn bud(
        &self,
        value: Ident,
        arrow: ThisArg<(Atom, SyntaxContext)>,
        output: &TCfg,
        out_block: Id<TBlock>,
        stmt: &TStmt,
        d: Id<TBlock>,
        argv: Ident,
        func: &TFunc,
    ) -> Self {
        Splatting {
            cache: Default::default(),
            catch: output.blocks[out_block].post.catch.clone(),
            ret: Some((stmt.left.clone(), d, argv)),
            this_val: if (!func.cfg.has_this()) {
                self.this_val.clone()
            } else {
                match arrow {
                    ThisArg::NoThisArg => Some((Atom::new("globalThis"), Default::default())),
                    ThisArg::This => self.this_val.clone(),
                    ThisArg::Val(a) => Some(a),
                }
            },
            stack: self.stack.iter().cloned().chain([value]).collect(),
        }
    }
    fn sub(
        &self,
        mut out_block: Id<TBlock>,
        output: &mut TCfg,
        value: Ident,
        arrow: ThisArg<(Atom, SyntaxContext)>,
        stmt: &TStmt,
        func: &TFunc,
        args: &[SpreadOr<Ident>],
        map: Mapper<'_>,
    ) -> (Id<TBlock>) {
        let argv = output.regs.alloc(());
        output.decls.insert(argv.clone());
        output.blocks[out_block].stmts.push(TStmt {
            left: LId::Id { id: argv.clone() },
            flags: ValFlags::SSA_LIKE,
            right: Item::Arr {
                members: args.iter().cloned().collect(),
            },
            span: Span::dummy_with_cmt(),
        });
        if args.iter().any(|a| a.is_spread) {
            for (i, param) in func.params.iter().cloned().enumerate() {
                output.blocks[out_block].stmts.push(TStmt {
                    left: LId::Id { id: param.clone() },
                    flags: Default::default(),
                    right: Item::Lit {
                        lit: Lit::Num(Number {
                            value: i as f64,
                            raw: None,
                            span: Span::dummy_with_cmt(),
                        }),
                    },
                    span: Span::dummy_with_cmt(),
                });
                output.blocks[out_block].stmts.push(TStmt {
                    left: LId::Id { id: param.clone() },
                    flags: Default::default(),
                    right: Item::Mem {
                        obj: argv.clone(),
                        mem: param.clone(),
                    },
                    span: Span::dummy_with_cmt(),
                });
            }
        } else {
            for (param, arg) in func
                .params
                .iter()
                .cloned()
                .map(Some)
                .chain(once(None).cycle())
                .zip(args.iter().cloned().map(Some).chain(once(None).cycle()))
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
                            Some(SpreadOr { value: a, .. }) => Item::Just { id: a },
                        },
                        span: Span::dummy_with_cmt(),
                    });
                }
            }
        }
        // if {
        let mut d = output.blocks.alloc(Default::default());
        output.blocks[d].post.catch = output.blocks[out_block].post.catch.clone();
        let mut new = self.bud(value, arrow, output, out_block, stmt, d, argv, &func);
        let c = new.translate(&func.cfg, output, func.entry, map.bud());
        output.blocks[replace(&mut out_block, d)].post.term = TTerm::Jmp(c);
        return out_block;
        // continue 'b;
    }
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
                if let Some((_, _, a)) = self.ret.as_ref() {
                    if let Item::Arguments = &mut stmt.right {
                        stmt.right = Item::Just { id: a.clone() }
                    }
                }
                if let Item::Call { callee, args } = &stmt.right {
                    macro_rules! func {
                        ($value:expr, $func:expr, $arrow:expr) => {
                            match $func {
                                func => match $arrow {
                                    arrow => {
                                        out_block = self.sub(
                                            out_block,
                                            output,
                                            $value,
                                            arrow,
                                            &stmt,
                                            &func,
                                            args,
                                            map.bud(),
                                        );
                                        continue 'b;
                                    }
                                },
                            }
                        };
                    }
                    match callee {
                        TCallee::Val(value) => {
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
                                                if let Ok(g) =
                                                    (map.to_cfg)(&f.function).and_then(|a| {
                                                        TFunc::try_from_with_mapper(&a, map.bud())
                                                    })
                                                {
                                                    func!(value, g, ThisArg::<Ident>::This)
                                                }
                                            }
                                            _ => {}
                                        }
                                    }
                                    if let Some((func, arrow)) =
                                        output.func_and_this(value.clone(), None, (), &Verbatim)
                                    {
                                        func!(value, func.clone(), arrow);
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
                        TCallee::Member {
                            func: value,
                            member,
                        } => {
                            if let Some((func, arrow)) = output.func_and_this(
                                value.clone(),
                                Some(member.clone()),
                                (),
                                &Verbatim,
                            ) {
                                func!(value.clone(), func.clone(), arrow);
                                // }
                            }
                        }
                        _ => {}
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
                                                match method.value.as_str().unwrap_or("nope") {
                                                    "call" => {
                                                        if let SpreadOr {
                                                            is_spread: false,
                                                            value: this_arg,
                                                        } = &args[0]
                                                        {
                                                            out_block = self.sub(
                                                                out_block,
                                                                output,
                                                                $value,
                                                                ThisArg::Val(this_arg.clone()),
                                                                &stmt,
                                                                &func,
                                                                &args[1..],
                                                                map.bud(),
                                                            );
                                                            continue 'b;
                                                        }
                                                    }
                                                    "apply" => {
                                                        if let SpreadOr {
                                                            is_spread: false,
                                                            value: this_arg,
                                                        } = &args[0]
                                                        {
                                                            if let SpreadOr {
                                                                is_spread: false,
                                                                value: args,
                                                            } = &args[1]
                                                            {
                                                                out_block = self.sub(
                                                                    out_block,
                                                                    output,
                                                                    $value,
                                                                    ThisArg::Val(this_arg.clone()),
                                                                    &stmt,
                                                                    &func,
                                                                    &[SpreadOr {
                                                                        is_spread: true,
                                                                        value: args.clone(),
                                                                    }],
                                                                    map.bud(),
                                                                );
                                                                continue 'b;
                                                            }
                                                        }
                                                    }
                                                    _ => {}
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
                    Some((id, b2, _)) => {
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
                    Some((id, b2, _)) => {
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
