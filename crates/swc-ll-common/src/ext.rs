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
/// Extension trait providing higher-level item resolution operations.
///
/// This trait builds on `ItemGetter` to provide more complex queries like
/// resolving primordial objects and native functions.
pub trait ItemGetterExt<I, F,Ctx>: ItemGetter<I, F,Ctx> {
    fn func_and_this<'a>(&'a self, i: I,ctx: Ctx) -> Option<(&'a F, ThisArg<I>)>
    where
        I: Clone + 'a,Ctx: Clone+'a,
    {
        match self.get_item(i,ctx.clone())? {
            Item::Func { func, arrow } => Some((
                func,
                if *arrow {
                    ThisArg::This
                } else {
                    ThisArg::GlobalThis
                },
            )),
            Item::Mem { obj, mem } => match self.get_item(obj.clone(),ctx.clone()) {
                // Item::Obj { members }
                _ => None,
            },
            _ => None,
        }
    }
    fn primordial(&self, i: I,ctx: Ctx) -> Option<&'static Primordial>
    where
        I: Clone,Ctx:Clone,
    {
        match self.get_ident(i.clone(),ctx.clone()) {
            Some((a, _)) => Primordial::global(&a),
            _ => match self.get_item(i,ctx.clone())? {
                Item::Mem { obj, mem } => match self.get_item(mem.clone(),ctx.clone())? {
                    Item::Lit { lit: Lit::Str(s) } => {
                        self.primordial(obj.clone(),ctx)?.get_perfect(s.value.as_str()?)
                    }
                    _ => None,
                },
                _ => None,
            },
        }
    }
    fn native_of(&self, mut i: I,ctx: Ctx) -> Option<Native<I>>
    where
        I: Clone,Ctx: Clone,
    {
        loop {
            let g = self.get_item(i,ctx.clone())?;
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
                if let Some(i) = self.get_ident(func.clone(),ctx.clone()) {
                    if i.0 == "globalThis" {
                        break;
                    }
                }
                let Item::Just { id } = self.get_item(func.clone(),ctx.clone())? else {
                    return None;
                };
                func = id;
            }
            let n = loop {
                let id = match self.get_item(member.clone(),ctx.clone())? {
                    Item::Lit { lit: Lit::Str(s) } => {
                        if let Some(m) = s.value.as_str().and_then(|s| s.strip_prefix("~Natives_"))
                        {
                            if let Some(m) = Native::of(m) {
                                break m;
                            }
                        }
                        return None;
                    }
                    Item::Just { id } => id,
                    _ => return None,
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
    fn inlinable(&self, d: &Item<I, F>,ctx: Ctx) -> bool
    where
        I: Clone,Ctx: Clone,
    {
        let tcfg = self;
        match d {
            Item::Just { id } => tcfg.get_item(id.clone(),ctx.clone()).is_some(),
            Item::Asm { value }
                if match value {
                    Asm::OrZero(value) => tcfg.get_item(value.clone(),ctx.clone()).is_some(),
                    _ => todo!(),
                } =>
            {
                true
            }
            Item::Lit { lit } => true,
            Item::Un { arg, op }
                if !matches!(op, UnaryOp::Delete) && tcfg.get_item(arg.clone(),ctx.clone()).is_some() =>
            {
                true
            }
            _ => false,
        }
    }
    fn simplify_just(&mut self, i: I,ctx: Ctx) -> bool
    where
        Item<I, F>: Clone,
        I: Clone,Ctx: Clone,
    {
        if let Some(g) = self.get_item(i.clone(),ctx.clone()).and_then(|j| match j {
            Item::Just { id } => self.get_item(id.clone(),ctx.clone()),
            _ => None,
        }) {
            if self.inlinable(g,ctx.clone()) {
                let g = g.clone();
                if let Some(h) = self.get_mut_item(i,ctx.clone()) {
                    *h = g;
                    return true;
                }
            }
        }
        return false;
    }
}
impl<T: ItemGetter<I, F,Ctx> + ?Sized, I, F,Ctx> ItemGetterExt<I, F,Ctx> for T {}
impl<I: Copy + Eq, F> Item<I, F> {
    pub fn const_in<Ctx: Clone>(
        &self,
        semantics: &SemanticCfg,
        k: &(dyn ItemGetter<I, F,Ctx> + '_),
        span: Span,
        ctx: Ctx,
    ) -> Option<Lit> {
        return match self {
            Item::Just { id } => None,
            Item::Bin {
                left: l2,
                right: r2,
                op,
            } => {
                if l2 == r2
                    && semantics
                        .flags
                        .contains(SemanticFlags::BITWISE_OR_ABSENT_NAN)
                {
                    match op {
                        BinaryOp::EqEqEq | BinaryOp::EqEq => {
                            return Some(Lit::Bool(Bool { span, value: true }));
                        }
                        BinaryOp::NotEqEq | BinaryOp::NotEq => {
                            return Some(Lit::Bool(Bool { span, value: false }));
                        }
                        _ => {}
                    }
                }
                let left = k.get_item(*l2,ctx.clone())?;
                let right = k.get_item(*r2,ctx.clone())?;
                let (left, right) = match (left, right) {
                    (Item::Undef, Item::Undef) => match op {
                        BinaryOp::EqEqEq | BinaryOp::EqEq => {
                            return Some(Lit::Bool(Bool { span, value: true }));
                        }
                        BinaryOp::NotEqEq | BinaryOp::NotEq => {
                            return Some(Lit::Bool(Bool { span, value: false }));
                        }
                        _ => {
                            let left = left.const_in(semantics, k, span,ctx.clone())?;
                            let right = right.const_in(semantics, k, span,ctx.clone())?;
                            (left, right)
                        }
                    },
                    (left_val, right_val) => {
                        let left = left_val.const_in(semantics, k, span,ctx.clone());
                        let right = right_val.const_in(semantics, k, span,ctx.clone());
                        match (left_val, right_val, &left, &right) {
                            (Item::Undef, _, _, Some(_)) | (_, Item::Undef, Some(_), _) => match op
                            {
                                BinaryOp::EqEqEq => {
                                    return Some(Lit::Bool(Bool { span, value: false }));
                                }
                                BinaryOp::NotEqEq => {
                                    return Some(Lit::Bool(Bool { span, value: true }));
                                }
                                _ => {
                                    // let left = left.const_in(semantics, k)?;
                                    // let right = right.const_in(semantics, k)?;
                                    (left?, right?)
                                }
                            },
                            // (_, r, Some(l), _)
                            //     if *op == op!("in")
                            //         && (!k.taints_object(*r2)
                            //             || semantics
                            //                 .flags
                            //                 .contains(SemanticFlags::ALL_OBJECTS_FROZEN))
                            //                  =>
                            // {
                            //     match r {
                            //         SValue::Item {
                            //             item: Item::Obj { members },
                            //             span,
                            //         } => match {
                            //             // let l = k.val(*mem).and_then(|m| m.const_in(semantics, k, pierce))?;
                            //             let mut i = members.iter();
                            //             loop {
                            //                 let Some(i) = i.next() else {
                            //                     break Some(false);
                            //                 };
                            //                 let l2 = match &i.0 {
                            //                     PropKey::Lit(PropSym {
                            //                         sym: l,
                            //                         span: s2,
                            //                         ctx: _,
                            //                     }) => Lit::Str(Str {
                            //                         span: span.clone().unwrap_or(*s2),
                            //                         value: l.clone().into(),
                            //                         raw: None,
                            //                     }),
                            //                     PropKey::Computed(c) => {
                            //                         match k.val(*c).and_then(|w| {
                            //                             w.const_in(semantics, k, pierce)
                            //                         }) {
                            //                             None => return None,
                            //                             Some(l) => l,
                            //                         }
                            //                     }
                            //                     _ => break None,
                            //                 };
                            //                 if l2 != *l {
                            //                     continue;
                            //                 };
                            //                 break Some(true);
                            //             }
                            //         } {
                            //             Some(v) => {
                            //                 return Some(Lit::Bool(Bool {
                            //                     span: span
                            //                         .clone()
                            //                         .unwrap_or(Span::dummy_with_cmt()),
                            //                     value: v,
                            //                 }));
                            //             }
                            //             None => (left?, right?),
                            //         },
                            //         _ => (left?, right?),
                            //     }
                            // }
                            (_, _, Some(v), Some(v2)) => (left?, right?),
                            _ => return None,
                        }
                    }
                };
                macro_rules! op2 {
                        ($left:expr_2021 => {$($op:tt)*} $right:expr_2021) => {
                            match (
                                Expr::Lit($left.clone()).as_pure_number(default_ctx()),
                                Expr::Lit($right.clone()).as_pure_number(default_ctx()),
                            ) {
                                (Value::Known(k), Value::Known(l))
                                    if !k.is_nan() && !l.is_nan() =>
                                {
                                    let sum = k $($op)* l;
                                    if sum.is_nan() {
                                        None
                                    } else {
                                        Some(Lit::Num(Number {
                                            span: left.span(),
                                            value: sum,
                                            raw: None,
                                        }))
                                    }
                                }
                                _ => None,
                            }
                        };
                    }
                macro_rules! bop2 {
                        ($left:expr_2021 => {$($op:tt)*} $right:expr_2021) => {
                            match (
                                Expr::Lit($left.clone()).as_pure_number(default_ctx()),
                                Expr::Lit($right.clone()).as_pure_number(default_ctx()),
                            ) {
                                (Value::Known(k), Value::Known(l))
                                    if !k.is_nan() && !l.is_nan() =>
                                {
                                    let sum = k $($op)* l;
                                    Some(Lit::Bool(Bool{
                                        span: left.span(),
                                        value: sum,
                                    }))
                                }
                                _ => None,
                            }
                        };
                    }
                macro_rules! iop2 {
                        ($left:expr_2021 => {$($op:tt)*} $right:expr_2021) => {
                            match (
                                Expr::Lit($left.clone()).as_pure_number(default_ctx()),
                                Expr::Lit($right.clone()).as_pure_number(default_ctx()),
                            ) {
                                (Value::Known(k), Value::Known(l))
                                    if !k.is_nan() && !l.is_nan() =>
                                {
                                    let k: i32 = num_traits::cast(k)?;
                                    let l: i32 = num_traits::cast(l)?;
                                    let sum = k $($op)* l;
                                    let sum = sum as f64;
                                    if sum.is_nan() {
                                        None
                                    } else {
                                        Some(Lit::Num(Number {
                                            span: left.span(),
                                            value: sum,
                                            raw: None,
                                        }))
                                    }
                                }
                                _ => None,
                            }
                        };
                    }
                match op {
                    BinaryOp::Add => {
                        match (
                            Expr::Lit(left.clone()).as_pure_string(default_ctx()),
                            Expr::Lit(right.clone()).as_pure_string(default_ctx()),
                        ) {
                            (Value::Known(k), Value::Known(l)) => Some(Lit::Str(Str {
                                span: left.span(),
                                value: Atom::new(format!("{k}{l}")).into(),
                                raw: None,
                            })),
                            _ => match (
                                Expr::Lit(left.clone()).as_pure_number(default_ctx()),
                                Expr::Lit(right.clone()).as_pure_number(default_ctx()),
                            ) {
                                (Value::Known(k), Value::Known(l))
                                    if !k.is_nan() && !l.is_nan() =>
                                {
                                    let sum = k + l;
                                    if sum.is_nan() {
                                        None
                                    } else {
                                        Some(Lit::Num(Number {
                                            span: left.span(),
                                            value: sum,
                                            raw: None,
                                        }))
                                    }
                                }
                                _ => None,
                            },
                        }
                    }
                    op!(bin, "-") => op2!(left => {-} right),
                    op!("/") => op2!(left => {/} right),
                    op!("%") => op2!(left => {%} right),
                    op!("*") => op2!(left => {*} right),
                    op!("<<") => iop2!(left => {<<} right),
                    op!(">>") => iop2!(left => {>>} right),
                    op!("**") => match (
                        Expr::Lit(left.clone()).as_pure_number(default_ctx()),
                        Expr::Lit(right.clone()).as_pure_number(default_ctx()),
                    ) {
                        (Value::Known(k), Value::Known(l)) if !k.is_nan() && !l.is_nan() => {
                            let sum = k.powf(l);
                            if sum.is_nan() {
                                None
                            } else {
                                Some(Lit::Num(Number {
                                    span: left.span(),
                                    value: sum,
                                    raw: None,
                                }))
                            }
                        }
                        _ => None,
                    },
                    op!(">>>") => match (
                        Expr::Lit(left.clone()).as_pure_number(default_ctx()),
                        Expr::Lit(right.clone()).as_pure_number(default_ctx()),
                    ) {
                        (Value::Known(k), Value::Known(l)) if !k.is_nan() && !l.is_nan() => {
                            let k: i32 = num_traits::cast(k)?;
                            let k = k as u32;
                            let l: i32 = num_traits::cast(l)?;
                            let l = l as u32;
                            let sum = k << l;
                            let sum = sum as i32 as f64;
                            if sum.is_nan() {
                                None
                            } else {
                                Some(Lit::Num(Number {
                                    span: left.span(),
                                    value: sum,
                                    raw: None,
                                }))
                            }
                        }
                        _ => None,
                    },
                    op!("&") => iop2!(left => {&} right),
                    op!("|") => iop2!(left => {|} right),
                    op!("^") => iop2!(left => {^} right),
                    op!("<") => bop2!(left => {<} right),
                    op!("<=") => bop2!(left => {<=} right),
                    op!(">") => bop2!(left => {>} right),
                    op!(">=") => bop2!(left => {>=} right),
                    op!("===") => Some(Lit::Bool(Bool {
                        span: left.span(),
                        value: left.eq_ignore_span(&right),
                    })),
                    op!("!==") => Some(Lit::Bool(Bool {
                        span: left.span(),
                        value: !left.eq_ignore_span(&right),
                    })),
                    _ => None,
                }
            }
            Item::Un { arg, op } => {
                if let UnaryOp::Void = op {
                    return Some(Lit::Num(Number {
                        value: 0.0,
                        span: Span::dummy_with_cmt(),
                        raw: None,
                    }));
                }
                let l = k.get_item(*arg,ctx.clone())?.const_in(semantics, k, span,ctx.clone())?;
                match op {
                    swc_ecma_ast::UnaryOp::Minus => match l {
                        Lit::Num(n) => Some(Lit::Num(Number {
                            value: -n.value,
                            span: n.span,
                            raw: n.raw,
                        })),
                        _ => None,
                    },
                    swc_ecma_ast::UnaryOp::Plus => {
                        let x = Expr::Lit(l);
                        let synth = <Expr as ExprExt>::as_pure_number(&x, default_ctx());
                        match synth {
                            Value::Known(k) if !k.is_nan() => Some(Lit::Num(Number {
                                span: x.span(),
                                value: k,
                                raw: None,
                            })),
                            _ => None,
                        }
                    }
                    swc_ecma_ast::UnaryOp::Bang => {
                        let x = Expr::Lit(l);
                        let synth = x.as_pure_bool(default_ctx());
                        match synth {
                            Value::Known(k) => Some(Lit::Bool(Bool {
                                span: x.span(),
                                value: !k,
                            })),
                            _ => None,
                        }
                    }
                    swc_ecma_ast::UnaryOp::Tilde => {
                        let x = Expr::Lit(l);
                        let synth = <Expr as ExprExt>::as_pure_number(&x, default_ctx());
                        match synth {
                            Value::Known(value) if value.fract() == 0.0 => Some(Lit::Num(Number {
                                span: x.span(),
                                value: if value < 0.0 {
                                    !(value as i32 as u32) as i32 as f64
                                } else {
                                    !(value as u32) as i32 as f64
                                },
                                raw: None,
                            })),
                            _ => None,
                        }
                    }
                    swc_ecma_ast::UnaryOp::TypeOf => None,
                    swc_ecma_ast::UnaryOp::Void => todo!(),
                    swc_ecma_ast::UnaryOp::Delete => None,
                }
            }
            Item::Mem { obj, mem } => {
                match k.get_item(*obj,ctx.clone()) {
                    Some(Item::Obj { members },
                   ) => match {
                        let l = k.get_item(*mem,ctx.clone()).and_then(|m| m.const_in(semantics, k, span,ctx.clone()))?;
                        let mut i = members.iter();
                        loop {
                            let Some(i) = i.next() else {
                                break None;
                            };
                            let l2 = match &i.0 {
                                PropKey::Lit(PropSym {
                                    sym: l,
                                    span: s2,
                                    ctx: _,
                                }) => Lit::Str(Str {
                                    span,
                                    value: l.clone().into(),
                                    raw: None,
                                }),
                                PropKey::Computed(c) => {
                                    match k.get_item(*c,ctx.clone()).and_then(|w| w.const_in(semantics, k, span,ctx.clone())) {
                                        None => return None,
                                        Some(l) => l,
                                    }
                                }
                                _ => break None,
                            };
                            if l2 != l {
                                continue;
                            };
                            let PropVal::Item(i) = &i.1 else {
                                break None;
                            };
                            break Some(*i);
                        }
                    } {
                        Some(v) => {
                            return k.get_item(v,ctx.clone()).and_then(|w| w.const_in(semantics, k, span,ctx.clone()));
                        }
                        None => {}
                    },
                    _ => {}
                }
                match k.get_item(*mem,ctx.clone()).and_then(|m| m.const_in(semantics, k, span,ctx.clone())) {
                        // Some(Lit::Str(s)) => match s.value.as_str()? {
                        //     "length" => match k.val(*obj) {
                        //         Some(i)
                        //             if semantics
                        //                 .flags
                        //                 .contains(SemanticFlags::NO_MONKEYPATCHING) =>
                        //         {
                        //             match i.array_in(semantics, k, pierce) {
                        //                 None => {
                        //                     let l = i.const_in(semantics, k, pierce)?;
                        //                     let Lit::Str(s) = l else {
                        //                         return None;
                        //                     };
                        //                     Some(Lit::Num(Number {
                        //                         span: s.span,
                        //                         value: s.value.len() as f64,
                        //                         raw: None,
                        //                     }))
                        //                 }
                        //                 Some(a) => Some(Lit::Num(Number {
                        //                     span: span
                        //                         .as_ref()
                        //                         .cloned()
                        //                         .unwrap_or_else(|| Span::dummy_with_cmt()),
                        //                     value: a.len() as f64,
                        //                     raw: None,
                        //                 })),
                        //             }
                        //         }
                        //         _ => None,
                        //     },
                        //     _ => None,
                        // },
                        // Some(Lit::Num(n)) => {
                        //     match k.val(*obj) {
                        //         Some(i)
                        //             if semantics
                        //                 .flags
                        //                 .contains(SemanticFlags::NO_MONKEYPATCHING) =>
                        //         {
                        //             match i.array_in(semantics, k, pierce) {
                        //             None => None,
                        //             Some(a) => a
                        //                 .iter()
                        //                 .all(|SpreadOr { value: _, is_spread: v }| !*v)
                        //                 .then(|| {
                        //                     a.get((n.value.round() as usize))
                        //                         .and_then(|SpreadOr { value: a, is_spread: _ }| k.val(*a))
                        //                         .and_then(|a| a.const_in(semantics, k, pierce))
                        //                 })
                        //                 .flatten(),
                        //         }
                        //         }
                        //         _ => None,
                        //     }
                        // }
                        _ => None,
                    }
            }
            Item::Call { callee, args }
                if semantics.flags.contains(SemanticFlags::NO_MONKEYPATCHING) =>
            {
                match callee {
                    TCallee::Member { func, member } => {
                        let member = k.get_item(*member,ctx.clone())?.const_in(semantics, k, span,ctx.clone())?;
                        let Lit::Str(s) = member else {
                            return None;
                        };
                        let func = k.get_item(*func,ctx.clone())?;
                        match func {
                            _ => {
                                let func = func.const_in(semantics, k, span,ctx.clone())?;
                                let mut i;
                                let ses = ses_method(
                                    &func,
                                    s.value.as_str()?,
                                    &mut match args.iter() {
                                        i2 => {
                                            i = i2;
                                            std::iter::from_fn(|| {
                                                let SpreadOr {
                                                    value: n,
                                                    is_spread: s,
                                                } = i.next()?;
                                                let i =
                                                    k.get_item(*n,ctx.clone())?.const_in(semantics, k, span,ctx.clone())?;
                                                Some(i)
                                            })
                                            .fuse()
                                        }
                                    },
                                )?;
                                Some(ses)
                            }
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };
    }
}
