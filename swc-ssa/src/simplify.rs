use crate::*;
use portal_jsc_swc_util::{SemanticCfg, SemanticFlags};
use swc_atoms::Atom;
use swc_common::{EqIgnoreSpan, Spanned, SyntaxContext};
use swc_ecma_ast::{BinaryOp, Bool, Expr, Number, Str, UnaryOp, op};
use swc_ecma_utils::{ExprCtx, ExprExt, Value};

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
pub trait SValGetter<I: Copy, B, F = SFunc> {
    fn val(&self, id: I) -> Option<&SValue<I, B, F>>;
}
impl SValGetter<Id<SValueW>, Id<SBlock>> for SCfg {
    fn val(&self, id: Id<SValueW>) -> Option<&SValue<Id<SValueW>, Id<SBlock>>> {
        Some(&self.values[id].value)
    }
}
pub(crate) fn default_ctx() -> ExprCtx {
    ExprCtx {
        unresolved_ctxt: SyntaxContext::empty(),
        is_unresolved_ref_safe: false,
        in_strict: true,
        remaining_depth: 4,
    }
}
impl<I: Copy, B, F> SValue<I, B, F>
where
    Self: PartialEq,
{
    pub fn const_in(&self, semantics: &SemanticCfg, k: &impl SValGetter<I, B, F>) -> Option<Lit> {
        match self {
            SValue::Item { item, span } => match item {
                Item::Just { id } => None,
                Item::Bin { left, right, op } => {
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
                        (a, b)
                            if a == b
                                && semantics
                                    .flags
                                    .contains(SemanticFlags::BITWISE_OR_ABSENT_NAN) =>
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
                                _ => {
                                    let left = left.const_in(semantics, k)?;
                                    let right = right.const_in(semantics, k)?;
                                    (left, right)
                                }
                            }
                        }
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
                                Some(SValue::Item {
                                    item: Item::Arr { members },
                                    span,
                                }) if semantics.flags.contains(SemanticFlags::ASSUME_SES) => {
                                    Some(Lit::Num(Number {
                                        span: span
                                            .as_ref()
                                            .cloned()
                                            .unwrap_or_else(|| Span::dummy_with_cmt()),
                                        value: members.len() as f64,
                                        raw: None,
                                    }))
                                }
                                _ => None,
                            },
                            _ => None,
                        },
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
