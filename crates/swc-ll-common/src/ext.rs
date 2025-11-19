use std::mem::replace;

use super::*;
use swc_ecma_ast::op;
use swc_ecma_utils::{ExprCtx, ExprExt, Value};
pub fn default_ctx() -> ExprCtx {
    ExprCtx {
        unresolved_ctxt: SyntaxContext::empty(),
        is_unresolved_ref_safe: false,
        in_strict: true,
        remaining_depth: 4,
    }
}
pub trait ItemResultGetter<I: Clone, F, Ctx: Clone, R> {
    fn get_result(
        &self,
        // semantics: &SemanticCfg,
        g: &(dyn ItemGetter<I, F, Ctx> + '_),
        i: I,
        ctx: Ctx,
    ) -> Option<R>;
}
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default, Hash, Debug)]
pub struct Verbatim;

impl<I: Clone, F, Ctx: Clone> ItemResultGetter<I, F, Ctx, Lit> for Verbatim {
    fn get_result(
        &self,
        // semantics: &SemanticCfg,
        g: &(dyn ItemGetter<I, F, Ctx> + '_),
        i: I,
        ctx: Ctx,
    ) -> Option<Lit> {
        match g.get_item(i, ctx)? {
            Item::Lit { lit } => Some(lit.clone()),
            _ => None,
        }
    }
}
#[derive(Clone)]
pub enum ForceEquality {
    Lit(Lit),
    Undef,
}
#[derive(Clone)]
pub enum ForceTarget {
    Eq(ForceEquality),
    Ne(ForceEquality),
}
/// Extension trait providing higher-level item resolution operations.
///
/// This trait builds on `ItemGetter` to provide more complex queries like
/// resolving primordial objects and native functions.
pub trait ItemGetterExt<I, F, Ctx>: ItemGetter<I, F, Ctx> {
    fn func_and_this<'a>(
        &'a self,
        i: I,
        member: Option<I>,
        ctx: Ctx,
        l: &(dyn ItemResultGetter<I, F, Ctx, Lit> + '_),
    ) -> Option<(&'a F, ThisArg<I>)>
    where
        I: Clone + 'a,
        Ctx: Clone + 'a,
    {
        match member {
            None => match self.get_item(i, ctx.clone())? {
                Item::Func { func, arrow } => Some((
                    func,
                    if *arrow {
                        ThisArg::This
                    } else {
                        ThisArg::NoThisArg
                    },
                )),
                _ => None,
            },
            Some(mem) => {
                let Lit::Str(str) = l.get_result(&self, mem.clone(), ctx.clone())? else {
                    return None;
                };
                match match self.get_item(i.clone(), ctx.clone())? {
                    Item::Obj { members }
                        if members.iter().all(|i| matches!(&i.0, PropKey::Lit(_))) =>
                    {
                        members.iter().find_map(|(k, v)| {
                            let PropKey::Lit(k) = k else { unreachable!() };
                            if k.sym.as_bytes() != str.value.as_bytes() {
                                return None;
                            };
                            match v {
                                PropVal::Item(i) => {
                                    self.func_and_this(i.clone(), None, ctx.clone(), l)
                                }
                                PropVal::Method(m) => Some((m, ThisArg::NoThisArg)),
                                _ => None,
                            }
                        })
                    }
                    _ => None,
                } {
                    None => None,
                    Some((a, _)) => Some((a, ThisArg::Val(i.clone()))),
                }
            }
        }
    }
    fn primordial(
        &self,
        // semantics: &SemanticCfg,
        i: I,
        ctx: Ctx,
        l: &(dyn ItemResultGetter<I, F, Ctx, Lit> + '_),
    ) -> Option<&'static Primordial>
    where
        I: Clone,
        Ctx: Clone,
    {
        match self.get_ident(i.clone(), ctx.clone()) {
            Some((a, _)) => Primordial::global(&a),
            _ => match self.get_item(i, ctx.clone())? {
                Item::Mem { obj, mem } => match l.get_result(&self, mem.clone(), ctx.clone()) {
                    Some(Lit::Str(s)) => self
                        .primordial(obj.clone(), ctx, l)?
                        .get_perfect(s.value.as_str()?),
                    _ => None,
                },
                _ => None,
            },
        }
    }
    fn native_of(
        &self,
        // semantics: &SemanticCfg,
        mut i: I,
        ctx: Ctx,
        l: &(dyn ItemResultGetter<I, F, Ctx, Lit> + '_),
    ) -> Option<Native<I>>
    where
        I: Clone,
        Ctx: Clone,
    {
        loop {
            let g = self.get_item(i, ctx.clone())?;
            let (mut func, mut member, args) = match g {
                Item::Just { id } => {
                    i = id.clone();
                    continue;
                }
                Item::Call {
                    callee: TCallee::Member { func, member },
                    args,
                } => (func, member, args),
                _ => return None,
            };
            loop {
                if let Some(i) = self.get_ident(func.clone(), ctx.clone()) {
                    if i.0 == "globalThis" {
                        break;
                    }
                }
                let Item::Just { id } = self.get_item(func.clone(), ctx.clone())? else {
                    return None;
                };
                func = id;
            }
            let n = loop {
                let id = match l.get_result(&self, member.clone(), ctx.clone()) {
                    Some(Lit::Str(s)) => {
                        if let Some(m) = s.value.as_str().and_then(|s| s.strip_prefix("~Natives_"))
                        {
                            if let Some(m) = Native::of(m) {
                                break m;
                            }
                        }
                        return None;
                    }
                    _ => match self.get_item(member.clone(), ctx.clone())? {
                        Item::Lit { lit: Lit::Str(s) } => {
                            if let Some(m) =
                                s.value.as_str().and_then(|s| s.strip_prefix("~Natives_"))
                            {
                                if let Some(m) = Native::of(m) {
                                    break m;
                                }
                            }
                            return None;
                        }
                        Item::Just { id } => id,
                        _ => return None,
                    },
                };
                member = id;
            };
            let mut args = args.iter().cloned();
            return n
                .map::<I, ()>(&mut |_| match args.next() {
                    Some(SpreadOr {
                        value: a,
                        is_spread: b,
                    }) if !b => Ok(a),
                    _ => Err(()),
                })
                .ok();
        }
    }
    fn inlinable(&self, d: &Item<I, F>, ctx: Ctx) -> bool
    where
        I: Clone,
        Ctx: Clone,
    {
        let tcfg = self;
        match d {
            Item::Just { id } => tcfg.get_item(id.clone(), ctx.clone()).is_some(),
            Item::Asm { value }
                if match value {
                    Asm::OrZero(value) => tcfg.get_item(value.clone(), ctx.clone()).is_some(),
                    _ => todo!(),
                } =>
            {
                true
            }
            Item::Lit { lit } => true,
            Item::Un { arg, op }
                if !matches!(op, UnaryOp::Delete)
                    && tcfg.get_item(arg.clone(), ctx.clone()).is_some() =>
            {
                true
            }
            _ => false,
        }
    }
    fn simplify_just(&mut self, i: I, ctx: Ctx) -> bool
    where
        Item<I, F>: Clone,
        I: Clone,
        Ctx: Clone,
    {
        if let Some(g) = self.get_item(i.clone(), ctx.clone()).and_then(|j| match j {
            Item::Just { id } => self.get_item(id.clone(), ctx.clone()),
            _ => None,
        }) {
            if self.inlinable(g, ctx.clone()) {
                let g = g.clone();
                if let Some(h) = self.get_mut_item(i, ctx.clone()) {
                    *h = g;
                    return true;
                }
            }
        }
        return false;
    }
    fn force(
        &mut self,
        mut i: I,
        ctx: Ctx,
        l: &(dyn ItemResultGetter<I, F, Ctx, Lit> + '_),
        mut target: ForceTarget,
        trap: &mut bool,
    ) where
        I: Clone,
        Item<I, F>: Clone,
        Ctx: Clone,
    {
        'a: loop {
            match &target {
                ForceTarget::Eq(target) => match target {
                    ForceEquality::Lit(target) => {
                        if let Some(lit) = l.get_result(&self, i.clone(), ctx.clone()) {
                            if !lit.eq_ignore_span(&target) {
                                *trap = true;
                                return;
                            }
                        }
                    }
                    ForceEquality::Undef => {}
                },

                ForceTarget::Ne(target) => match target {
                    ForceEquality::Lit(target) => {
                        if let Some(lit) = l.get_result(&self, i.clone(), ctx.clone()) {
                            if lit.eq_ignore_span(&target) {
                                *trap = true;
                                return;
                            }
                        }
                    }
                    ForceEquality::Undef => {
                        if let Some(Item::Undef) = self.get_item(i.clone(), ctx.clone()) {
                            *trap = true;
                            return;
                        }
                    }
                },
            }

            let ir = self.get_mut_item(i.clone(), ctx.clone());
            let Some(ir) = ir else {
                return;
            };
            match (
                match &target {
                    ForceTarget::Eq(target) => replace(
                        ir,
                        match target {
                            ForceEquality::Lit(target) => Item::Lit {
                                lit: target.clone(),
                            },
                            ForceEquality::Undef => Item::Undef,
                        },
                    ),
                    _ => ir.clone(),
                },
                target,
            ) {
                (
                    Item::Bin {
                        left,
                        right,
                        op: BinaryOp::EqEqEq,
                    },
                    ForceTarget::Eq(ForceEquality::Lit(Lit::Bool(Bool { span, value: true })))
                    | ForceTarget::Ne(ForceEquality::Lit(Lit::Bool(Bool { span, value: false }))),
                )
                | (
                    Item::Bin {
                        left,
                        right,
                        op: BinaryOp::NotEqEq,
                    },
                    ForceTarget::Eq(ForceEquality::Lit(Lit::Bool(Bool { span, value: false })))
                    | ForceTarget::Ne(ForceEquality::Lit(Lit::Bool(Bool { span, value: true }))),
                ) => {
                    if let Some(left) = l.get_result(&self, left.clone(), ctx.clone()) {
                        i = right;
                        target = ForceTarget::Eq(ForceEquality::Lit(left));
                        continue 'a;
                    } else if let Some(right) = l.get_result(&self, right.clone(), ctx.clone()) {
                        i = left;
                        target = ForceTarget::Eq(ForceEquality::Lit(right));
                        continue 'a;
                    }

                    if let Some(Item::Undef) = self.get_item(left.clone(), ctx.clone()) {
                        i = right;
                        target = ForceTarget::Eq(ForceEquality::Undef);
                        continue 'a;
                    }
                    if let Some(Item::Undef) = self.get_item(right.clone(), ctx.clone()) {
                        i = left;
                        target = ForceTarget::Eq(ForceEquality::Undef);
                        continue 'a;
                    }

                    return;
                }
                (
                    Item::Bin {
                        left,
                        right,
                        op: BinaryOp::EqEqEq,
                    },
                    ForceTarget::Eq(ForceEquality::Lit(Lit::Bool(Bool { span, value: false })))
                    | ForceTarget::Ne(ForceEquality::Lit(Lit::Bool(Bool { span, value: true }))),
                )
                | (
                    Item::Bin {
                        left,
                        right,
                        op: BinaryOp::NotEqEq,
                    },
                    ForceTarget::Eq(ForceEquality::Lit(Lit::Bool(Bool { span, value: true })))
                    | ForceTarget::Ne(ForceEquality::Lit(Lit::Bool(Bool { span, value: false }))),
                ) => {
                    if let Some(left) = l.get_result(&self, left.clone(), ctx.clone()) {
                        i = right;
                        target = ForceTarget::Ne(ForceEquality::Lit(left));
                        continue 'a;
                    } else if let Some(right) = l.get_result(&self, right.clone(), ctx.clone()) {
                        i = left;
                        target = ForceTarget::Ne(ForceEquality::Lit(right));
                        continue 'a;
                    }
                    if let Some(Item::Undef) = self.get_item(left.clone(), ctx.clone()) {
                        i = right;
                        target = ForceTarget::Ne(ForceEquality::Undef);
                        continue 'a;
                    }
                    if let Some(Item::Undef) = self.get_item(right.clone(), ctx.clone()) {
                        i = left;
                        target = ForceTarget::Ne(ForceEquality::Undef);
                        continue 'a;
                    }
                    return;
                }
                (
                    Item::Select {
                        cond,
                        then,
                        otherwise,
                    },
                    ForceTarget::Ne(target2),
                ) => {
                    self.force(
                        otherwise,
                        ctx.clone(),
                        l,
                        ForceTarget::Ne(target2.clone()),
                        trap,
                    );

                    i = then;
                    target = ForceTarget::Ne(target2);
                    continue 'a;
                }
                (Item::Just { id }, target2) => {
                    i = id;
                    target = target2;
                    continue 'a;
                }
                _ => return,
            }
        }
    }
}
impl<T: ItemGetter<I, F, Ctx> + ?Sized, I, F, Ctx> ItemGetterExt<I, F, Ctx> for T {}
pub mod consts;
