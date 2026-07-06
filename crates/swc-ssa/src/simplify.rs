//! Simplification and optimization passes for SSA.
//!
//! This module provides various simplification and optimization transformations
//! on SSA form. These passes:
//! - Simplify conditional branches with constant conditions
//! - Eliminate redundant loads and stores
//! - Perform constant propagation
//! - Simplify operations with known values
//!
//! # Optimization Passes
//!
//! The simplifications work on the SSA CFG to:
//! - Reduce code size
//! - Eliminate dead code
//! - Constant fold operations
//! - Remove redundant memory operations
//!
//! # Key Traits
//!
//! - [`SValGetter`]: Trait for getting SSA value information

use crate::*;
use portal_jsc_swc_util::SemanticCfg;
use swc_tac::ItemGetterExt;
pub use swc_tac::{Item, ItemGetter};
<<<<<<< HEAD
use swc_tac::{SpreadOr, TCallee};
=======
use swc_tac::TCallee;
>>>>>>> origin/main
pub type _Ident = Ident;
impl SCfg {
    pub fn simplify_conditions(&mut self) {
        log::trace!("ssa simplify_conditions: checking {} blocks", self.blocks.len());
        for (_k, kd) in self.blocks.iter_mut() {
            if let STerm::CondJmp {
                cond,
                if_true,
                if_false,
            } = &mut kd.postcedent.term
                && let SValue::Item {
                    item: Item::Lit { lit: Lit::Bool(b) },
                    span: _,
                } = &self.values[*cond].value
            {
                log::trace!(
                    "ssa simplify_conditions: folding constant CondJmp (value={}) → Jmp",
                    b.value
                );
                kd.postcedent.term = STerm::Jmp(if b.value {
                    if_true.clone()
                } else {
                    if_false.clone()
                })
            }
        }
    }
    pub fn simplify_loads(&mut self) {
        log::trace!("ssa simplify_loads: scanning {} blocks", self.blocks.len());
        for (_k, kd) in self.blocks.iter() {
            let mut m = BTreeMap::new();
            for s in kd.stmts.iter().cloned() {
                let x = &mut self.values[s];
                if let SValueW {
                    value: SValue::LoadId(i),
                } = x
                    && let Some(g) = m.get(&*i)
                {
                    *x = SValueW {
                        value: SValue::Item {
                            item: Item::Just { id: *g },
                            span: None,
                        },
                    }
                }
                if let SValueW {
                    value: SValue::StoreId { target, val },
                } = x
                {
                    m.insert(target.clone(), *val);
                }
            }
        }
    }
    pub fn simplify_justs(&mut self) {
        log::trace!("ssa simplify_justs: iterating over {} values", self.values.len());
        let mut redo = true;
        while take(&mut redo) {
            for ref_ in self.values.iter().map(|a| a.0).collect::<BTreeSet<_>>() {
                redo |= ItemGetterExt::<crate::SValueId, SFunc, SSACtx<'_, ()>>::simplify_just(
                    &mut *self,
                    ref_,
                    SSACtx {
                        wrapped: &(),
                        pierce: true,
                    },
                );
            }
        }
    }
    /// Inlines direct calls to immediately-invoked function expressions whose body is a
    /// single, straight-line block: no internal control flow, no nested closures, no named
    /// variable load/store, and (for a real `function`, not an arrow) no `this`/`arguments`
    /// reference. This is exactly the shape produced by e.g. `jade-vm-frontend`'s
    /// tenant-method `this`-rewrite (see the `jade` repo's
    /// `docs/pluggable-tenant-interface-plan.md` addendum) — a
    /// `(function(__this, ...params){ <straight-line ops>; return x; })(tenantRef, ...args)`
    /// splice. Anything not matching this narrow shape is left as an ordinary call: inlining
    /// here is purely an optimization, never required for correctness, so declining to inline
    /// is always a safe fallback.
    pub fn inline_iifes(&mut self) {
        log::trace!("ssa inline_iifes: scanning {} blocks", self.blocks.len());
        for block_id in self.blocks.iter().map(|(id, _)| id).collect::<Vec<_>>() {
            let stmt_ids = self.blocks[block_id].stmts.clone();
            for stmt_id in stmt_ids {
                self.try_inline_iife(block_id, stmt_id);
            }
        }
    }
    /// Follows `Item::Just` alias chains to find an `Item::Func` literal, returning its
    /// `SFunc` and whether it's an arrow function.
    fn resolve_func_literal(&self, mut id: SValueId) -> Option<(SFunc, bool)> {
        loop {
            match &self.values[id].value {
                SValue::Item {
                    item: Item::Just { id: inner },
                    span: _,
                } => id = *inner,
                SValue::Item {
                    item: Item::Func { func, arrow },
                    span: _,
                } => return Some((func.clone(), *arrow)),
                _ => return None,
            }
        }
    }
    fn try_inline_iife(&mut self, block_id: SBlockId, call_id: SValueId) {
        let (callee_id, args, span) = match &self.values[call_id].value {
            SValue::Item {
                item:
                    Item::Call {
                        callee: TCallee::Val(callee_id),
                        args,
                    },
                span,
            } => (*callee_id, args.clone(), *span),
            _ => return,
        };
        if args.iter().any(|a| a.is_spread) {
            return;
        }
        let args: Vec<SValueId> = args.into_iter().map(|a| a.value).collect();
        let Some((func, arrow)) = self.resolve_func_literal(callee_id) else {
            return;
        };
        if func.is_generator || func.is_async {
            return;
        }
<<<<<<< HEAD
        if func.cfg.blocks[func.entry].params.len() != args.len() {
            return;
        }
        // Walk the callee as a straight-line *chain* of blocks joined only by unconditional
        // `Jmp`s (the shape a trivial function body reliably round-trips to, even with no
        // source-level branching at all — TAC/SSA conversion doesn't guarantee a single
        // block for a single-`return` function). Any real branching (`CondJmp`/`Switch`),
        // exception handling (`Throw`/an active `catch`), or a revisited block (a loop) is
        // rejected: those aren't "straight-line" and are out of scope for this pass.
        let mut rename: BTreeMap<SValueId, SValueId> = BTreeMap::new();
        for (param, arg) in func.cfg.blocks[func.entry].params.iter().zip(args.iter()) {
            rename.insert(param.0, *arg);
        }
        let mut spliced = Vec::new();
        let mut current = func.entry;
        let mut visited: BTreeSet<SBlockId> = BTreeSet::new();
        let ret_id: Option<SValueId> = loop {
            if !visited.insert(current) {
                return;
            }
            let block = &func.cfg.blocks[current];
            if block.postcedent.catch != SCatch::Throw {
                return;
            }
            // Soundness scan: only plain computed values (no nested closures; no
            // named-variable load/store; and, for a real `function` rather than an arrow,
            // no `this`/`arguments`, since those would be rebound by splicing into the
            // caller's own context).
            for &sid in &block.stmts {
                match &func.cfg.values[sid].value {
                    SValue::Item { item, span: _ } => {
                        if item.funcs().next().is_some() {
                            return;
                        }
                        if !arrow && matches!(item, Item::This | Item::Arguments) {
                            return;
                        }
                    }
                    _ => return,
                }
            }
            for &sid in &block.stmts {
                let SValue::Item { item, span } = func.cfg.values[sid].value.clone() else {
                    unreachable!("checked above: every callee stmt is SValue::Item");
                };
                let item = item
                    .map2(
                        &mut (),
                        &mut |_cx: &mut (), id: SValueId| -> Result<SValueId, Infallible> {
                            Ok(*rename.get(&id).expect(
                                "IIFE inlining: callee body referenced a value outside the \
                                 chain of blocks walked so far",
                            ))
                        },
                        &mut |_cx: &mut (), func: SFunc| -> Result<SFunc, Infallible> { Ok(func) },
                    )
                    .unwrap();
                let new_id = self.values.alloc(SValue::Item { item, span }.into());
                rename.insert(sid, new_id);
                spliced.push(new_id);
            }
            match &block.postcedent.term {
                TTerm::Return(ret) => break *ret,
                TTerm::Jmp(target) => {
                    let Some(next_params) = func.cfg.blocks.get(target.block).map(|b| &b.params) else {
                        return;
                    };
                    if next_params.len() != target.args.len() {
                        return;
                    }
                    for (param, arg) in next_params.iter().zip(target.args.iter()) {
                        let Some(renamed_arg) = rename.get(arg).copied() else {
                            return;
                        };
                        rename.insert(param.0, renamed_arg);
                    }
                    current = target.block;
                }
                // `return f(...)` in source lowers to a tail call, not `Return(Some(call_id))`
                // — synthesize the equivalent `Item::Call` directly in the caller (renaming
                // through the same map as everything else) and treat its result as what the
                // callee "returned".
                TTerm::Tail { callee, args } => {
                    if args.iter().any(|a| a.is_spread) {
                        return;
                    }
                    let Ok(new_callee) = callee.clone().map(&mut |id| rename.get(&id).copied().ok_or(())) else {
                        return;
                    };
                    let mut new_args = Vec::with_capacity(args.len());
                    for a in args {
                        let Some(v) = rename.get(&a.value).copied() else {
                            return;
                        };
                        new_args.push(SpreadOr { value: v, is_spread: false });
                    }
                    let new_call_id = self.values.alloc(
                        SValue::Item {
                            item: Item::Call { callee: new_callee, args: new_args },
                            span: None,
                        }
                        .into(),
                    );
                    spliced.push(new_call_id);
                    // `new_call_id` is already a caller-space id (just allocated in `self`),
                    // unlike `TTerm::Return`'s callee-space id below — self-map it so the
                    // uniform `rename.get(&r)` lookup after the loop still resolves it.
                    rename.insert(new_call_id, new_call_id);
                    break Some(new_call_id);
                }
                _ => return,
            }
        };
        let new_ret = match ret_id {
            Some(r) => match rename.get(&r) {
                Some(id) => Some(*id),
                None => return,
            },
            None => None,
        };
=======
        if func.cfg.blocks.len() != 1 {
            return;
        }
        let entry_block = &func.cfg.blocks[func.entry];
        if entry_block.params.len() != args.len() {
            return;
        }
        if entry_block.postcedent.catch != SCatch::Throw {
            return;
        }
        let ret_id = match &entry_block.postcedent.term {
            TTerm::Return(ret) => *ret,
            _ => return,
        };
        // Soundness scan: only plain computed values (no nested closures; no named-variable
        // load/store; and, for a real `function` rather than an arrow, no `this`/`arguments`,
        // since those would be rebound by splicing into the caller's own context).
        for &sid in &entry_block.stmts {
            match &func.cfg.values[sid].value {
                SValue::Item { item, span: _ } => {
                    if item.funcs().next().is_some() {
                        return;
                    }
                    if !arrow && matches!(item, Item::This | Item::Arguments) {
                        return;
                    }
                }
                _ => return,
            }
        }
        // Map the callee's own entry-block params to the call's actual argument values, then
        // copy the rest of the body into fresh caller-arena values, renaming references as we
        // go (definitions precede uses within a single SSA block, so the rename map is always
        // populated by the time it's needed).
        let mut rename: BTreeMap<SValueId, SValueId> = BTreeMap::new();
        for (param, arg) in entry_block.params.iter().zip(args.iter()) {
            rename.insert(param.0, *arg);
        }
        let mut spliced = Vec::with_capacity(entry_block.stmts.len());
        for &sid in &entry_block.stmts {
            let SValue::Item { item, span } = func.cfg.values[sid].value.clone() else {
                unreachable!("checked above: every callee stmt is SValue::Item");
            };
            let item = item
                .map2(
                    &mut (),
                    &mut |_cx: &mut (), id: SValueId| -> Result<SValueId, Infallible> {
                        Ok(*rename.get(&id).expect(
                            "IIFE inlining: callee body referenced a value outside its own \
                             single block",
                        ))
                    },
                    &mut |_cx: &mut (), func: SFunc| -> Result<SFunc, Infallible> { Ok(func) },
                )
                .unwrap();
            let new_id = self.values.alloc(SValue::Item { item, span }.into());
            rename.insert(sid, new_id);
            spliced.push(new_id);
        }
        let new_ret = ret_id.map(|r| rename[&r]);
>>>>>>> origin/main
        // Splice the callee's body into the caller block right before the call, and alias the
        // call's own result to whatever the callee returned (`undefined` if it fell off the
        // end without an explicit `return`).
        let block = &mut self.blocks[block_id];
        let pos = block
            .stmts
            .iter()
            .position(|&s| s == call_id)
            .expect("call_id must be a statement of block_id");
        block.stmts.splice(pos..pos, spliced);
        self.values[call_id].value = match new_ret {
            Some(id) => SValue::Item {
                item: Item::Just { id },
                span,
            },
            None => SValue::Item {
                item: Item::Undef,
                span,
            },
        };
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Copy, PartialOrd, Ord)]
pub struct SSACtx<'a, Ctx> {
    pub wrapped: &'a Ctx,
    pub pierce: bool,
}
pub trait SValGetter<I: Copy + Eq, B, F = SFunc, Ctx = ()>:
    for<'a> ItemGetter<I, F, SSACtx<'a, Ctx>>
{
    fn val(&self, id: I, ctx: Ctx) -> Option<&SValue<I, B, F>>;
    fn val_mut(&mut self, id: I, ctx: Ctx) -> Option<&mut SValue<I, B, F>>;
    fn inputs<'a>(
        &'a self,
        _block: &B,
        _param: usize,
        _ctx: Ctx,
    ) -> Box<dyn Iterator<Item = I> + 'a>
    where
        I: 'a,
        B: 'a,
    {
        Box::new(empty())
    }
    fn input<'a>(&'a self, block: &B, param: usize, ctx: Ctx) -> Option<I>
    where
        I: 'a,
        B: 'a,
    {
        let mut i = self.inputs(block, param, ctx);
        let n = i.next()?;
        for o in i {
            if o != n {
                return None;
            }
        }
        Some(n)
    }
    fn taints_object(&self, _id: I, _ctx: Ctx) -> bool {
        true
    }
}
#[doc(hidden)]
pub fn _get_item<'a, I: Copy + Eq, B, F, Ctx: Clone>(
    a: &'a (dyn SValGetter<I, B, F, Ctx> + 'a),
    mut i: I,
    ctx: SSACtx<'_, Ctx>,
) -> Option<&'a Item<I, F>> {
    loop {
        match a.val(i, ctx.wrapped.clone())? {
            SValue::Param { block, idx, ty: _ } => {
                if ctx.pierce
                    && let Some(j) = a.input(block, *idx, ctx.wrapped.clone())
                {
                    i = j;
                    continue;
                }
                return None;
            }
            SValue::Item { item, span: _ } => return Some(item),
            SValue::Assign { target: _, val } => {
                i = *val;
            }
            SValue::LoadId(_) => return None,
            SValue::StoreId { target: _, val } => {
                i = *val;
            }
            SValue::EdgeBlocker { value, span: _ } => {
                i = *value;
            }
        }
    }
}
#[doc(hidden)]
pub fn _get_ident<'a, I: Copy + Eq, B, F, Ctx: Clone>(
    a: &'a (dyn SValGetter<I, B, F, Ctx> + 'a),
    mut i: I,
    ctx: SSACtx<'a, Ctx>,
) -> Option<Ident> {
    let mut bak = None;
    loop {
        match a.val(i, ctx.wrapped.clone())? {
            SValue::Param { block, idx, ty: _ } => {
                if ctx.pierce
                    && let Some(j) = a.input(block, *idx, ctx.wrapped.clone())
                {
                    i = j;
                    continue;
                };
                return bak;
            }
            SValue::Item { item, span: _ } => match item {
                Item::Just { id } => {
                    i = *id;
                }
                _ => return bak,
            },
            SValue::Assign { target: _, val } => {
                i = *val;
            }
            SValue::LoadId(a) => return Some(a.clone()),
            SValue::StoreId { target, val } => {
                bak = Some(target.clone());
                i = *val;
            }
            SValue::EdgeBlocker { value, span: _ } => {
                i = *value;
            }
        }
    }
}
#[doc(hidden)]
pub fn _get_item_mut<'a, 'b: 'a, I: Copy + Eq, B, F, Ctx: Clone>(
    a: &'b mut (dyn SValGetter<I, B, F, Ctx> + 'a),
    mut i: I,
    ctx: SSACtx<'_, Ctx>,
) -> Option<&'a mut Item<I, F>> {
    let a: *mut (dyn SValGetter<I, B, F, Ctx> + 'a) = a as *mut _;
    loop {
        //SAFETY: only borrowed once; values are moved before continuing the loop
        match unsafe { &mut *a }.val_mut(i, ctx.wrapped.clone())? {
            SValue::Param { block, idx, ty: _ } => {
                if ctx.pierce
                    && let Some(j) = unsafe { &mut *a }.input(block, *idx, ctx.wrapped.clone())
                {
                    i = j;
                    continue;
                };
                return None;
            }
            SValue::Item { item, span: _ } => return Some(item),
            SValue::Assign { target: _, val } => {
                i = *val;
            }
            SValue::LoadId(_) => return None,
            SValue::StoreId { target: _, val } => {
                i = *val;
            }
            SValue::EdgeBlocker { value, span: _ } => {
                i = *value;
            }
        }
    }
}
#[macro_export]
macro_rules! sval_item {
    ($(<$($a:tt)*>)? $ty:ty [block $block:ty]) => {
        impl<'a,$($($a)*,)?I: Copy + Eq,F,Ctx:Clone> $crate::simplify::ItemGetter<I,F,$crate::simplify::SSACtx<'a,Ctx>> for $ty where Self: $crate::simplify::SValGetter<I,$block,F,Ctx>{
            fn get_item<'b>(&'b self, i: I,ctx: $crate::simplify::SSACtx<'a,Ctx>) -> Option<&'b $crate::simplify::Item<I, F>> where Ctx: 'b{
                $crate::simplify::_get_item(self,i,ctx)
            }
            fn get_mut_item<'b>(&'b mut self, i: I,ctx: $crate::simplify::SSACtx<'a,Ctx>) -> Option<&'b mut $crate::simplify::Item<I, F>> where Ctx: 'b{
                $crate::simplify::_get_item_mut(self,i,ctx)
            }
            fn get_ident<'b>(&'b self, i: I,ctx: $crate::simplify::SSACtx<'a,Ctx>) -> Option<$crate::simplify::_Ident> where Ctx: 'b{
                $crate::simplify::_get_ident(self,i,ctx)
            }
        }
    };
}
impl<Ctx: Clone> SValGetter<crate::SValueId, SBlockId, SFunc, Ctx> for SCfg {
    fn val(&self, id: crate::SValueId, _ctx: Ctx) -> Option<&SValue<crate::SValueId, SBlockId>> {
        Some(&self.values[id].value)
    }
    fn val_mut(
        &mut self,
        id: crate::SValueId,
        _ctx: Ctx,
    ) -> Option<&mut SValue<crate::SValueId, SBlockId, SFunc>> {
        Some(&mut self.values[id].value)
    }
    fn inputs<'a>(
        &'a self,
        block: &SBlockId,
        param: usize,
        _ctx: Ctx,
    ) -> Box<dyn Iterator<Item = crate::SValueId> + 'a>
    where
        crate::SValueId: 'a,
        SBlockId: 'a,
    {
        Box::new(SCfg::inputs(self, *block, param))
    }
    fn taints_object(&self, id: crate::SValueId, _ctx: Ctx) -> bool {
        SCfg::taints_object(self, &id)
    }
}
sval_item!(SCfg [block SBlockId]);

// impl<I: Copy + Eq, B: Clone, F> SValue<I, B, F> {
//     pub fn array_in(
//         &self,
//         semantics: &SemanticCfg,
//         k: &(dyn SValGetter<I, B, F> + '_),
//         pierce: bool,
//     ) -> Option<Vec<SpreadOr<I>>> {
//         match self {
//             SValue::Param { block, idx, ty } if pierce => {
//                 let mut i = k
//                     .inputs(block.clone(), *idx)
//                     .filter_map(|i| k.val(i))
//                     .filter_map(|t| t.array_in(semantics, k, pierce));
//                 let mut n = i.next()?;
//                 for j in i {
//                     if j != n {
//                         return None;
//                     }
//                 }
//                 Some(n)
//             }
//             SValue::Item { item, span } => {
//                 match item {
//                     Item::Arr { members } => Some(members.clone()),
//                     Item::Mem { obj, mem } => {
//                         match k.val(*mem).and_then(|m| m.const_in(semantics, k, pierce)) {
//                             Some(Lit::Num(n)) => match k.val(*obj) {
//                                 Some(i)
//                                     if semantics
//                                         .flags
//                                         .contains(SemanticFlags::NO_MONKEYPATCHING) =>
//                                 {
//                                     match i.array_in(semantics, k, pierce) {
//                                         None => None,
//                                         Some(a) => {
//                                             if a.iter().any(|SpreadOr { value: _, is_spread: v }| *v) {
//                                             return None;
//                                         };
//                                             a
//                                         .get((n.value.round() as usize))
//                                         .and_then(|SpreadOr { value: a, is_spread: _ }| k.val(*a))
//                                         .and_then(|a| a.array_in(semantics, k, pierce))
//                                         }
//                                     }
//                                 }
//                                 _ => None,
//                             },
//                             _ => None,
//                         }
//                     }
//                     Item::Call { callee, args }
//                         if semantics.flags.contains(SemanticFlags::NO_MONKEYPATCHING) =>
//                     {
//                         match callee {
//                             TCallee::Member { func, member } => {
//                                 let member = k.val(*member)?.const_in(semantics, k, pierce)?;
//                                 let Lit::Str(s) = member else {
//                                     return None;
//                                 };
//                                 let func = k.val(*func)?;
//                                 match func.array_in(semantics, k, pierce) {
//                                     Some(members) => match s.value.as_str()? {
//                                         "concat" => {
//                                             let mut members: Vec<SpreadOr<I>> = members;
//                                             for SpreadOr {
//                                                 value: a,
//                                                 is_spread: s,
//                                             } in args.iter().cloned()
//                                             {
//                                                 let a = k.val(a)?;
//                                                 let i = a.array_in(semantics, k, pierce)?;
//                                                 if s {
//                                                     return None;
//                                                 } else {
//                                                     members.extend(i);
//                                                 }
//                                             }
//                                             Some(members)
//                                         }
//                                         "slice" => {
//                                             let begin: Option<usize> = args
//                                             .get(0)
//                                             .cloned().and_then(|SpreadOr { value: a, is_spread: b }|(!b).then(move||a))
//                                             .and_then(|a| k.val(a))
//                                             .and_then(|v| v.const_in(semantics, k, pierce))
//                                             .and_then(|v| v.as_num().map(|a| a.value as usize));
//                                             let end: Option<usize> = args
//                                             .get(1)
//                                             .cloned().and_then(|SpreadOr { value: a, is_spread: b }|(!b).then(move||a))
//                                             .and_then(|a| k.val(a))
//                                             .and_then(|v| v.const_in(semantics, k, pierce))
//                                             .and_then(|v| v.as_num().map(|a| a.value as usize));
//                                             let mut members: Vec<SpreadOr<I>> = members;
//                                             if members.iter().any(|SpreadOr { value: _, is_spread: v }| *v) {
//                                             return None;
//                                         }
//                                             members = match (begin, end) {
//                                                 (Some(a), Some(b)) => members.drain(a..b).collect(),
//                                                 (None, None) => members,
//                                                 (None, Some(a)) => members.drain(..a).collect(),
//                                                 (Some(a), None) => members.drain(a..).collect(),
//                                             };
//                                             Some(members)
//                                         }
//                                         _ => None,
//                                     },
//                                     _ => None,
//                                 }
//                             }
//                             _ => None,
//                         }
//                     }
//                     _ => None,
//                 }
//             }
//             _ => None,
//         }
//     }
//     pub fn const_in(
//         &self,
//         semantics: &SemanticCfg,
//         k: &(dyn SValGetter<I, B, F> + '_),
//         pierce: bool,
//     ) -> Option<Lit> {
//         match self {
//             SValue::Param { block, idx, ty } if pierce => {
//                 let mut i = k.inputs(block.clone(), *idx).filter_map(|i| k.val(i));
//                 let mut n = i.next()?.const_in(semantics, k, pierce)?;
//                 for j in i {
//                     let j = j.const_in(semantics, k, pierce)?;
//                     if j != n {
//                         return None;
//                     }
//                 }
//                 Some(n)
//             }
//             SValue::Item { item, span } => match item {
//                 Item::Just { id } => None,
//                 Item::Bin {
//                     left: l2,
//                     right: r2,
//                     op,
//                 } => {
//                     if l2 == r2
//                         && semantics
//                             .flags
//                             .contains(SemanticFlags::BITWISE_OR_ABSENT_NAN)
//                     {
//                         match op {
//                             BinaryOp::EqEqEq | BinaryOp::EqEq => {
//                                 return Some(Lit::Bool(Bool {
//                                     span: span
//                                         .as_ref()
//                                         .cloned()
//                                         .unwrap_or_else(|| Span::dummy_with_cmt()),
//                                     value: true,
//                                 }));
//                             }
//                             BinaryOp::NotEqEq | BinaryOp::NotEq => {
//                                 return Some(Lit::Bool(Bool {
//                                     span: span
//                                         .as_ref()
//                                         .cloned()
//                                         .unwrap_or_else(|| Span::dummy_with_cmt()),
//                                     value: false,
//                                 }));
//                             }
//                             _ => {}
//                         }
//                     }
//                     let left = k.val(*l2)?;
//                     let right = k.val(*r2)?;
//                     let (left, right) = match (left, right) {
//                         (
//                             SValue::Item {
//                                 item: Item::Undef,
//                                 span: _,
//                             },
//                             SValue::Item {
//                                 item: Item::Undef,
//                                 span: _,
//                             },
//                         ) => match op {
//                             BinaryOp::EqEqEq | BinaryOp::EqEq => {
//                                 return Some(Lit::Bool(Bool {
//                                     span: span
//                                         .as_ref()
//                                         .cloned()
//                                         .unwrap_or_else(|| Span::dummy_with_cmt()),
//                                     value: true,
//                                 }));
//                             }
//                             BinaryOp::NotEqEq | BinaryOp::NotEq => {
//                                 return Some(Lit::Bool(Bool {
//                                     span: span
//                                         .as_ref()
//                                         .cloned()
//                                         .unwrap_or_else(|| Span::dummy_with_cmt()),
//                                     value: false,
//                                 }));
//                             }
//                             _ => {
//                                 let left = left.const_in(semantics, k, pierce)?;
//                                 let right = right.const_in(semantics, k, pierce)?;
//                                 (left, right)
//                             }
//                         },
//                         (left_val, right_val) => {
//                             let left = left_val.const_in(semantics, k, pierce);
//                             let right = right_val.const_in(semantics, k, pierce);
//                             match (left_val, right_val, &left, &right) {
//                                 (
//                                     SValue::Item {
//                                         item: Item::Undef,
//                                         span: _,
//                                     },
//                                     _,
//                                     _,
//                                     Some(_),
//                                 )
//                                 | (
//                                     _,
//                                     SValue::Item {
//                                         item: Item::Undef,
//                                         span: _,
//                                     },
//                                     Some(_),
//                                     _,
//                                 ) => match op {
//                                     BinaryOp::EqEqEq => {
//                                         return Some(Lit::Bool(Bool {
//                                             span: span
//                                                 .as_ref()
//                                                 .cloned()
//                                                 .unwrap_or_else(|| Span::dummy_with_cmt()),
//                                             value: false,
//                                         }));
//                                     }
//                                     BinaryOp::NotEqEq => {
//                                         return Some(Lit::Bool(Bool {
//                                             span: span
//                                                 .as_ref()
//                                                 .cloned()
//                                                 .unwrap_or_else(|| Span::dummy_with_cmt()),
//                                             value: true,
//                                         }));
//                                     }
//                                     _ => {
//                                         // let left = left.const_in(semantics, k)?;
//                                         // let right = right.const_in(semantics, k)?;
//                                         (left?, right?)
//                                     }
//                                 },
//                                 (_, r, Some(l), _)
//                                     if *op == op!("in")
//                                         && pierce
//                                         && (!k.taints_object(*r2)
//                                             || semantics
//                                                 .flags
//                                                 .contains(SemanticFlags::ALL_OBJECTS_FROZEN)) =>
//                                 {
//                                     match r {
//                                         SValue::Item {
//                                             item: Item::Obj { members },
//                                             span,
//                                         } => match {
//                                             // let l = k.val(*mem).and_then(|m| m.const_in(semantics, k, pierce))?;
//                                             let mut i = members.iter();
//                                             loop {
//                                                 let Some(i) = i.next() else {
//                                                     break Some(false);
//                                                 };
//                                                 let l2 = match &i.0 {
//                                                     PropKey::Lit(PropSym {
//                                                         sym: l,
//                                                         span: s2,
//                                                         ctx: _,
//                                                     }) => Lit::Str(Str {
//                                                         span: span.clone().unwrap_or(*s2),
//                                                         value: l.clone().into(),
//                                                         raw: None,
//                                                     }),
//                                                     PropKey::Computed(c) => {
//                                                         match k.val(*c).and_then(|w| {
//                                                             w.const_in(semantics, k, pierce)
//                                                         }) {
//                                                             None => return None,
//                                                             Some(l) => l,
//                                                         }
//                                                     }
//                                                     _ => break None,
//                                                 };
//                                                 if l2 != *l {
//                                                     continue;
//                                                 };
//                                                 break Some(true);
//                                             }
//                                         } {
//                                             Some(v) => {
//                                                 return Some(Lit::Bool(Bool {
//                                                     span: span
//                                                         .clone()
//                                                         .unwrap_or(Span::dummy_with_cmt()),
//                                                     value: v,
//                                                 }));
//                                             }
//                                             None => (left?, right?),
//                                         },
//                                         _ => (left?, right?),
//                                     }
//                                 }
//                                 (_, _, Some(v), Some(v2)) => (left?, right?),
//                                 _ => return None,
//                             }
//                         }
//                     };
//                     macro_rules! op2 {
//                         ($left:expr_2021 => {$($op:tt)*} $right:expr_2021) => {
//                             match (
//                                 Expr::Lit($left.clone()).as_pure_number(default_ctx()),
//                                 Expr::Lit($right.clone()).as_pure_number(default_ctx()),
//                             ) {
//                                 (Value::Known(k), Value::Known(l))
//                                     if !k.is_nan() && !l.is_nan() =>
//                                 {
//                                     let sum = k $($op)* l;
//                                     if sum.is_nan() {
//                                         None
//                                     } else {
//                                         Some(Lit::Num(Number {
//                                             span: left.span(),
//                                             value: sum,
//                                             raw: None,
//                                         }))
//                                     }
//                                 }
//                                 _ => None,
//                             }
//                         };
//                     }
//                     macro_rules! bop2 {
//                         ($left:expr_2021 => {$($op:tt)*} $right:expr_2021) => {
//                             match (
//                                 Expr::Lit($left.clone()).as_pure_number(default_ctx()),
//                                 Expr::Lit($right.clone()).as_pure_number(default_ctx()),
//                             ) {
//                                 (Value::Known(k), Value::Known(l))
//                                     if !k.is_nan() && !l.is_nan() =>
//                                 {
//                                     let sum = k $($op)* l;
//                                     Some(Lit::Bool(Bool{
//                                         span: left.span(),
//                                         value: sum,
//                                     }))
//                                 }
//                                 _ => None,
//                             }
//                         };
//                     }
//                     macro_rules! iop2 {
//                         ($left:expr_2021 => {$($op:tt)*} $right:expr_2021) => {
//                             match (
//                                 Expr::Lit($left.clone()).as_pure_number(default_ctx()),
//                                 Expr::Lit($right.clone()).as_pure_number(default_ctx()),
//                             ) {
//                                 (Value::Known(k), Value::Known(l))
//                                     if !k.is_nan() && !l.is_nan() =>
//                                 {
//                                     let k: i32 = num_traits::cast(k)?;
//                                     let l: i32 = num_traits::cast(l)?;
//                                     let sum = k $($op)* l;
//                                     let sum = sum as f64;
//                                     if sum.is_nan() {
//                                         None
//                                     } else {
//                                         Some(Lit::Num(Number {
//                                             span: left.span(),
//                                             value: sum,
//                                             raw: None,
//                                         }))
//                                     }
//                                 }
//                                 _ => None,
//                             }
//                         };
//                     }
//                     match op {
//                         BinaryOp::Add => {
//                             match (
//                                 Expr::Lit(left.clone()).as_pure_string(default_ctx()),
//                                 Expr::Lit(right.clone()).as_pure_string(default_ctx()),
//                             ) {
//                                 (Value::Known(k), Value::Known(l)) => Some(Lit::Str(Str {
//                                     span: left.span(),
//                                     value: Atom::new(format!("{k}{l}")).into(),
//                                     raw: None,
//                                 })),
//                                 _ => match (
//                                     Expr::Lit(left.clone()).as_pure_number(default_ctx()),
//                                     Expr::Lit(right.clone()).as_pure_number(default_ctx()),
//                                 ) {
//                                     (Value::Known(k), Value::Known(l))
//                                         if !k.is_nan() && !l.is_nan() =>
//                                     {
//                                         let sum = k + l;
//                                         if sum.is_nan() {
//                                             None
//                                         } else {
//                                             Some(Lit::Num(Number {
//                                                 span: left.span(),
//                                                 value: sum,
//                                                 raw: None,
//                                             }))
//                                         }
//                                     }
//                                     _ => None,
//                                 },
//                             }
//                         }
//                         op!(bin, "-") => op2!(left => {-} right),
//                         op!("/") => op2!(left => {/} right),
//                         op!("%") => op2!(left => {%} right),
//                         op!("*") => op2!(left => {*} right),
//                         op!("<<") => iop2!(left => {<<} right),
//                         op!(">>") => iop2!(left => {>>} right),
//                         op!("**") => match (
//                             Expr::Lit(left.clone()).as_pure_number(default_ctx()),
//                             Expr::Lit(right.clone()).as_pure_number(default_ctx()),
//                         ) {
//                             (Value::Known(k), Value::Known(l)) if !k.is_nan() && !l.is_nan() => {
//                                 let sum = k.powf(l);
//                                 if sum.is_nan() {
//                                     None
//                                 } else {
//                                     Some(Lit::Num(Number {
//                                         span: left.span(),
//                                         value: sum,
//                                         raw: None,
//                                     }))
//                                 }
//                             }
//                             _ => None,
//                         },
//                         op!(">>>") => match (
//                             Expr::Lit(left.clone()).as_pure_number(default_ctx()),
//                             Expr::Lit(right.clone()).as_pure_number(default_ctx()),
//                         ) {
//                             (Value::Known(k), Value::Known(l)) if !k.is_nan() && !l.is_nan() => {
//                                 let k: i32 = num_traits::cast(k)?;
//                                 let k = k as u32;
//                                 let l: i32 = num_traits::cast(l)?;
//                                 let l = l as u32;
//                                 let sum = k << l;
//                                 let sum = sum as i32 as f64;
//                                 if sum.is_nan() {
//                                     None
//                                 } else {
//                                     Some(Lit::Num(Number {
//                                         span: left.span(),
//                                         value: sum,
//                                         raw: None,
//                                     }))
//                                 }
//                             }
//                             _ => None,
//                         },
//                         op!("&") => iop2!(left => {&} right),
//                         op!("|") => iop2!(left => {|} right),
//                         op!("^") => iop2!(left => {^} right),
//                         op!("<") => bop2!(left => {<} right),
//                         op!("<=") => bop2!(left => {<=} right),
//                         op!(">") => bop2!(left => {>} right),
//                         op!(">=") => bop2!(left => {>=} right),
//                         op!("===") => Some(Lit::Bool(Bool {
//                             span: left.span(),
//                             value: left.eq_ignore_span(&right),
//                         })),
//                         op!("!==") => Some(Lit::Bool(Bool {
//                             span: left.span(),
//                             value: !left.eq_ignore_span(&right),
//                         })),
//                         _ => None,
//                     }
//                 }
//                 Item::Un { arg, op } => {
//                     if let UnaryOp::Void = op {
//                         return Some(Lit::Num(Number {
//                             value: 0.0,
//                             span: Span::dummy_with_cmt(),
//                             raw: None,
//                         }));
//                     }
//                     let l = k.val(*arg)?.const_in(semantics, k, pierce)?;
//                     match op {
//                         swc_ecma_ast::UnaryOp::Minus => match l {
//                             Lit::Num(n) => Some(Lit::Num(Number {
//                                 value: -n.value,
//                                 span: n.span,
//                                 raw: n.raw,
//                             })),
//                             _ => None,
//                         },
//                         swc_ecma_ast::UnaryOp::Plus => {
//                             let x = Expr::Lit(l);
//                             let synth = <Expr as ExprExt>::as_pure_number(&x, default_ctx());
//                             match synth {
//                                 Value::Known(k) if !k.is_nan() => Some(Lit::Num(Number {
//                                     span: x.span(),
//                                     value: k,
//                                     raw: None,
//                                 })),
//                                 _ => None,
//                             }
//                         }
//                         swc_ecma_ast::UnaryOp::Bang => {
//                             let x = Expr::Lit(l);
//                             let synth = x.as_pure_bool(default_ctx());
//                             match synth {
//                                 Value::Known(k) => Some(Lit::Bool(Bool {
//                                     span: x.span(),
//                                     value: !k,
//                                 })),
//                                 _ => None,
//                             }
//                         }
//                         swc_ecma_ast::UnaryOp::Tilde => {
//                             let x = Expr::Lit(l);
//                             let synth = <Expr as ExprExt>::as_pure_number(&x, default_ctx());
//                             match synth {
//                                 Value::Known(value) if value.fract() == 0.0 => {
//                                     Some(Lit::Num(Number {
//                                         span: x.span(),
//                                         value: if value < 0.0 {
//                                             !(value as i32 as u32) as i32 as f64
//                                         } else {
//                                             !(value as u32) as i32 as f64
//                                         },
//                                         raw: None,
//                                     }))
//                                 }
//                                 _ => None,
//                             }
//                         }
//                         swc_ecma_ast::UnaryOp::TypeOf => None,
//                         swc_ecma_ast::UnaryOp::Void => todo!(),
//                         swc_ecma_ast::UnaryOp::Delete => None,
//                     }
//                 }
//                 Item::Mem { obj, mem } => {
//                     match k.val(*obj) {
//                         Some(SValue::Item {
//                             item: Item::Obj { members },
//                             span,
//                         }) => match {
//                             let l = k.val(*mem).and_then(|m| m.const_in(semantics, k, pierce))?;
//                             let mut i = members.iter();
//                             loop {
//                                 let Some(i) = i.next() else {
//                                     break None;
//                                 };
//                                 let l2 = match &i.0 {
//                                     PropKey::Lit(PropSym {
//                                         sym: l,
//                                         span: s2,
//                                         ctx: _,
//                                     }) => Lit::Str(Str {
//                                         span: span.clone().unwrap_or(*s2),
//                                         value: l.clone().into(),
//                                         raw: None,
//                                     }),
//                                     PropKey::Computed(c) => {
//                                         match k
//                                             .val(*c)
//                                             .and_then(|w| w.const_in(semantics, k, pierce))
//                                         {
//                                             None => return None,
//                                             Some(l) => l,
//                                         }
//                                     }
//                                     _ => break None,
//                                 };
//                                 if l2 != l {
//                                     continue;
//                                 };
//                                 let PropVal::Item(i) = &i.1 else {
//                                     break None;
//                                 };
//                                 break Some(*i);
//                             }
//                         } {
//                             Some(v) => {
//                                 return k.val(v).and_then(|w| w.const_in(semantics, k, pierce));
//                             }
//                             None => {}
//                         },
//                         _ => {}
//                     }
//                     match k.val(*mem).and_then(|m| m.const_in(semantics, k, pierce)) {
//                         Some(Lit::Str(s)) => match s.value.as_str()? {
//                             "length" => match k.val(*obj) {
//                                 Some(i)
//                                     if semantics
//                                         .flags
//                                         .contains(SemanticFlags::NO_MONKEYPATCHING) =>
//                                 {
//                                     match i.array_in(semantics, k, pierce) {
//                                         None => {
//                                             let l = i.const_in(semantics, k, pierce)?;
//                                             let Lit::Str(s) = l else {
//                                                 return None;
//                                             };
//                                             Some(Lit::Num(Number {
//                                                 span: s.span,
//                                                 value: s.value.len() as f64,
//                                                 raw: None,
//                                             }))
//                                         }
//                                         Some(a) => Some(Lit::Num(Number {
//                                             span: span
//                                                 .as_ref()
//                                                 .cloned()
//                                                 .unwrap_or_else(|| Span::dummy_with_cmt()),
//                                             value: a.len() as f64,
//                                             raw: None,
//                                         })),
//                                     }
//                                 }
//                                 _ => None,
//                             },
//                             _ => None,
//                         },
//                         Some(Lit::Num(n)) => {
//                             match k.val(*obj) {
//                                 Some(i)
//                                     if semantics
//                                         .flags
//                                         .contains(SemanticFlags::NO_MONKEYPATCHING) =>
//                                 {
//                                     match i.array_in(semantics, k, pierce) {
//                                     None => None,
//                                     Some(a) => a
//                                         .iter()
//                                         .all(|SpreadOr { value: _, is_spread: v }| !*v)
//                                         .then(|| {
//                                             a.get((n.value.round() as usize))
//                                                 .and_then(|SpreadOr { value: a, is_spread: _ }| k.val(*a))
//                                                 .and_then(|a| a.const_in(semantics, k, pierce))
//                                         })
//                                         .flatten(),
//                                 }
//                                 }
//                                 _ => None,
//                             }
//                         }
//                         _ => None,
//                     }
//                 }
//                 Item::Call { callee, args }
//                     if semantics.flags.contains(SemanticFlags::NO_MONKEYPATCHING) =>
//                 {
//                     match callee {
//                         TCallee::Member { func, member } => {
//                             let member = k.val(*member)?.const_in(semantics, k, pierce)?;
//                             let Lit::Str(s) = member else {
//                                 return None;
//                             };
//                             let func = k.val(*func)?;
//                             match func {
//                                 _ => {
//                                     let func = func.const_in(semantics, k, pierce)?;
//                                     let mut i;
//                                     let ses = ses_method(
//                                         &func,
//                                         s.value.as_str()?,
//                                         &mut match args.iter() {
//                                             i2 => {
//                                                 i = i2;
//                                                 std::iter::from_fn(|| {
//                                                     let SpreadOr {
//                                                         value: n,
//                                                         is_spread: s,
//                                                     } = i.next()?;
//                                                     let i = k
//                                                         .val(*n)?
//                                                         .const_in(semantics, k, pierce)?;
//                                                     Some(i)
//                                                 })
//                                                 .fuse()
//                                             }
//                                         },
//                                     )?;
//                                     Some(ses)
//                                 }
//                             }
//                         }
//                         _ => None,
//                     }
//                 }
//                 _ => None,
//             },
//             _ => None,
//         }
//     }
// }
impl<I: Copy + Eq, B, F> SValue<I, B, F> {
    pub fn const_in<Ctx: Clone>(
        &self,
        semantics: &SemanticCfg,
        k: &(dyn SValGetter<I, B, F, Ctx> + '_),
        pierce: bool,
        ctx: Ctx,
    ) -> Option<Lit> {
        match self {
            SValue::Param { block, idx, ty: _ } => {
                if pierce {
                    if let Some(i) = k
                        .input(block, *idx, ctx.clone())
                        .and_then(|a| k.val(a, ctx.clone()))
                    {
                        i.const_in(semantics, k, pierce, ctx)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            SValue::Item { item, span } => item.const_in(
                semantics,
                k,
                (*span).unwrap_or_default(),
                SSACtx {
                    wrapped: &ctx,
                    pierce,
                },
            ),
            SValue::Assign { target: _, val } => k
                .val(*val, ctx.clone())?
                .const_in(semantics, k, pierce, ctx),
            SValue::StoreId { target: _, val } => k
                .val(*val, ctx.clone())?
                .const_in(semantics, k, pierce, ctx),
            SValue::EdgeBlocker { value, span: _ } => k
                .val(*value, ctx.clone())?
                .const_in(semantics, k, pierce, ctx),
            _ => None,
        }
    }
}
