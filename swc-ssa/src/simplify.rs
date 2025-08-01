use crate::*;
use portal_jsc_swc_util::{SemanticCfg, SemanticFlags, ses_method};
use swc_atoms::Atom;
use swc_common::{EqIgnoreSpan, Spanned, SyntaxContext};
use swc_ecma_ast::{BinaryOp, Bool, Expr, Number, Str, UnaryOp, op};
use swc_ecma_utils::{ExprCtx, ExprExt, Value};
pub use swc_tac::{Item, ItemGetter};

impl SCfg {
    pub fn simplify_conditions(&mut self) {
        for (k, kd) in self.blocks.iter_mut() {
            if let STerm::CondJmp {
                cond,
                if_true,
                if_false,
            } = &mut kd.postcedent.term
            {
                if let SValue::Item {
                    item: Item::Lit { lit: Lit::Bool(b) },
                    span,
                } = &self.values[*cond].value
                {
                    kd.postcedent.term = STerm::Jmp(if b.value {
                        if_true.clone()
                    } else {
                        if_false.clone()
                    })
                }
            }
        }
    }
}

pub trait SValGetter<I: Copy, B, F = SFunc>: ItemGetter<I, F> {
    fn val(&self, id: I) -> Option<&SValue<I, B, F>>;
}
#[doc(hidden)]
pub fn _get_item<'a, I: Copy, B, F>(
    a: &'a (dyn SValGetter<I, B, F> + 'a),
    mut i: I,
) -> Option<&'a Item<I, F>> {
    loop {
        match a.val(i)? {
            SValue::Param { block, idx, ty } => return None,
            SValue::Item { item, span } => return Some(item),
            SValue::Assign { target, val } => {
                i = *val;
            }
            SValue::LoadId(_) => return None,
            SValue::StoreId { target, val } => {
                i = *val;
            }
            SValue::EdgeBlocker { value, span } => {
                i = *value;
            }
        }
    }
}
#[macro_export]
macro_rules! sval_item {
    ($(<$($a:tt)*>)? $ty:ty [block $block:ty]) => {
        impl<$($($a)*,)?I: Copy,F> $crate::simplify::ItemGetter<I,F> for $ty where Self: $crate::simplify::SValGetter<I,$block,F>{
fn get_item(&self, i: I) -> Option<&$crate::simplify::Item<I, F>>{
    $crate::simplify::_get_item(self,i)
}
        }
    };
}
impl SValGetter<Id<SValueW>, Id<SBlock>> for SCfg {
    fn val(&self, id: Id<SValueW>) -> Option<&SValue<Id<SValueW>, Id<SBlock>>> {
        Some(&self.values[id].value)
    }
}
sval_item!(SCfg [block Id<SBlock>]);
pub(crate) fn default_ctx() -> ExprCtx {
    ExprCtx {
        unresolved_ctxt: SyntaxContext::empty(),
        is_unresolved_ref_safe: false,
        in_strict: true,
        remaining_depth: 4,
    }
}
impl<I: Copy + Eq, B, F> SValue<I, B, F> {
    pub fn array_in(
        &self,
        semantics: &SemanticCfg,
        k: &(dyn SValGetter<I, B, F> + '_),
    ) -> Option<Vec<I>> {
        match self {
            SValue::Item { item, span } => match item {
                Item::Arr { members } => Some(members.clone()),
                Item::Mem { obj, mem } => {
                    match k.val(*mem).and_then(|m| m.const_in(semantics, k)) {
                        Some(Lit::Num(n)) => match k.val(*obj) {
                            Some(i) if semantics.flags.contains(SemanticFlags::ASSUME_SES) => {
                                match i.array_in(semantics, k) {
                                    None => None,
                                    Some(a) => a
                                        .get((n.value.round() as usize))
                                        .and_then(|a| k.val(*a))
                                        .and_then(|a| a.array_in(semantics, k)),
                                }
                            }
                            _ => None,
                        },
                        _ => None,
                    }
                }
                Item::Call { callee, args }
                    if semantics.flags.contains(SemanticFlags::ASSUME_SES) =>
                {
                    match callee {
                        TCallee::Member { func, member } => {
                            let member = k.val(*member)?.const_in(semantics, k)?;
                            let Lit::Str(s) = member else {
                                return None;
                            };
                            let func = k.val(*func)?;
                            match func.array_in(semantics, k) {
                                Some(members) => match s.value.as_str() {
                                    "concat" => {
                                        let mut members: Vec<I> = members;
                                        for a in args.iter().cloned() {
                                            let a = k.val(a)?;
                                            let i = a.array_in(semantics, k)?;
                                            members.extend(i);
                                        }
                                        Some(members)
                                    }
                                    "slice" => {
                                        let begin: Option<usize> = args
                                            .get(0)
                                            .cloned()
                                            .and_then(|a| k.val(a))
                                            .and_then(|v| v.const_in(semantics, k))
                                            .and_then(|v| v.as_num().map(|a| a.value as usize));
                                        let end: Option<usize> = args
                                            .get(1)
                                            .cloned()
                                            .and_then(|a| k.val(a))
                                            .and_then(|v| v.const_in(semantics, k))
                                            .and_then(|v| v.as_num().map(|a| a.value as usize));
                                        let mut members: Vec<I> = members;
                                        members = match (begin, end) {
                                            (Some(a), Some(b)) => members.drain(a..b).collect(),
                                            (None, None) => members,
                                            (None, Some(a)) => members.drain(..a).collect(),
                                            (Some(a), None) => members.drain(a..).collect(),
                                        };
                                        Some(members)
                                    }
                                    _ => None,
                                },
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }
    pub fn const_in(
        &self,
        semantics: &SemanticCfg,
        k: &(dyn SValGetter<I, B, F> + '_),
    ) -> Option<Lit> {
        match self {
            SValue::Item { item, span } => match item {
                Item::Just { id } => None,
                Item::Bin { left, right, op } => {
                    if left == right
                        && semantics
                            .flags
                            .contains(SemanticFlags::BITWISE_OR_ABSENT_NAN)
                    {
                        match op {
                            BinaryOp::EqEqEq | BinaryOp::EqEq => {
                                return Some(Lit::Bool(Bool {
                                    span: span
                                        .as_ref()
                                        .cloned()
                                        .unwrap_or_else(|| Span::dummy_with_cmt()),
                                    value: true,
                                }));
                            }
                            BinaryOp::NotEqEq | BinaryOp::NotEq => {
                                return Some(Lit::Bool(Bool {
                                    span: span
                                        .as_ref()
                                        .cloned()
                                        .unwrap_or_else(|| Span::dummy_with_cmt()),
                                    value: false,
                                }));
                            }
                            _ => {}
                        }
                    }
                    let left = k.val(*left)?;
                    let right = k.val(*right)?;
                    let (left, right) = match (left, right) {
                        (
                            SValue::Item {
                                item: Item::Undef,
                                span: _,
                            },
                            SValue::Item {
                                item: Item::Undef,
                                span: _,
                            },
                        ) => match op {
                            BinaryOp::EqEqEq | BinaryOp::EqEq => {
                                return Some(Lit::Bool(Bool {
                                    span: span
                                        .as_ref()
                                        .cloned()
                                        .unwrap_or_else(|| Span::dummy_with_cmt()),
                                    value: true,
                                }));
                            }
                            BinaryOp::NotEqEq | BinaryOp::NotEq => {
                                return Some(Lit::Bool(Bool {
                                    span: span
                                        .as_ref()
                                        .cloned()
                                        .unwrap_or_else(|| Span::dummy_with_cmt()),
                                    value: false,
                                }));
                            }
                            _ => {
                                let left = left.const_in(semantics, k)?;
                                let right = right.const_in(semantics, k)?;
                                (left, right)
                            }
                        },

                        (left_val, right_val) => {
                            let left = left_val.const_in(semantics, k);
                            let right = right_val.const_in(semantics, k);
                            match (left_val, right_val, &left, &right) {
                                (
                                    SValue::Item {
                                        item: Item::Undef,
                                        span: _,
                                    },
                                    _,
                                    _,
                                    Some(_),
                                )
                                | (
                                    _,
                                    SValue::Item {
                                        item: Item::Undef,
                                        span: _,
                                    },
                                    Some(_),
                                    _,
                                ) => match op {
                                    BinaryOp::EqEqEq => {
                                        return Some(Lit::Bool(Bool {
                                            span: span
                                                .as_ref()
                                                .cloned()
                                                .unwrap_or_else(|| Span::dummy_with_cmt()),
                                            value: false,
                                        }));
                                    }
                                    BinaryOp::NotEqEq => {
                                        return Some(Lit::Bool(Bool {
                                            span: span
                                                .as_ref()
                                                .cloned()
                                                .unwrap_or_else(|| Span::dummy_with_cmt()),
                                            value: true,
                                        }));
                                    }
                                    _ => {
                                        // let left = left.const_in(semantics, k)?;
                                        // let right = right.const_in(semantics, k)?;
                                        (left?, right?)
                                    }
                                },
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
                                    value: Atom::new(format!("{k}{l}")),
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
                    let l = k.val(*arg)?.const_in(semantics, k)?;
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
                                Value::Known(value) if value.fract() == 0.0 => {
                                    Some(Lit::Num(Number {
                                        span: x.span(),
                                        value: if value < 0.0 {
                                            !(value as i32 as u32) as i32 as f64
                                        } else {
                                            !(value as u32) as i32 as f64
                                        },
                                        raw: None,
                                    }))
                                }
                                _ => None,
                            }
                        }
                        swc_ecma_ast::UnaryOp::TypeOf => None,
                        swc_ecma_ast::UnaryOp::Void => todo!(),
                        swc_ecma_ast::UnaryOp::Delete => None,
                    }
                }
                Item::Mem { obj, mem } => {
                    match k.val(*mem).and_then(|m| m.const_in(semantics, k)) {
                        Some(Lit::Str(s)) => match &*s.value {
                            "length" => match k.val(*obj) {
                                Some(i) if semantics.flags.contains(SemanticFlags::ASSUME_SES) => {
                                    match i.array_in(semantics, k) {
                                        None => {
                                            let l = i.const_in(semantics, k)?;
                                            let Lit::Str(s) = l else {
                                                return None;
                                            };
                                            Some(Lit::Num(Number {
                                                span: s.span,
                                                value: s.value.len() as f64,
                                                raw: None,
                                            }))
                                        }
                                        Some(a) => Some(Lit::Num(Number {
                                            span: span
                                                .as_ref()
                                                .cloned()
                                                .unwrap_or_else(|| Span::dummy_with_cmt()),
                                            value: a.len() as f64,
                                            raw: None,
                                        })),
                                    }
                                }
                                _ => None,
                            },
                            _ => None,
                        },
                        Some(Lit::Num(n)) => match k.val(*obj) {
                            Some(i) if semantics.flags.contains(SemanticFlags::ASSUME_SES) => {
                                match i.array_in(semantics, k) {
                                    None => None,
                                    Some(a) => a
                                        .get((n.value.round() as usize))
                                        .and_then(|a| k.val(*a))
                                        .and_then(|a| a.const_in(semantics, k)),
                                }
                            }
                            _ => None,
                        },
                        _ => None,
                    }
                }
                Item::Call { callee, args }
                    if semantics.flags.contains(SemanticFlags::ASSUME_SES) =>
                {
                    match callee {
                        TCallee::Member { func, member } => {
                            let member = k.val(*member)?.const_in(semantics, k)?;
                            let Lit::Str(s) = member else {
                                return None;
                            };
                            let func = k.val(*func)?;
                            match func {
                                _ => {
                                    let func = func.const_in(semantics, k)?;
                                    let mut i;
                                    let ses = ses_method(
                                        &func,
                                        &s.value,
                                        &mut match args.iter() {
                                            i2 => {
                                                i = i2;
                                                std::iter::from_fn(|| {
                                                    let n = i.next()?;
                                                    let i = k.val(*n)?.const_in(semantics, k)?;
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
                Item::Func { func, arrow } => None,
                Item::Lit { lit } => Some(lit.clone()),
                Item::Call { callee, args } => None,
                Item::Obj { members } => None,
                Item::Arr { members } => None,
                Item::Yield { value, delegate } => None,
                Item::Await { value } => None,
                Item::Undef => None,
                _ => None,
            },
            _ => None,
        }
    }
}
