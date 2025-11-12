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
use portal_jsc_swc_util::{SemanticCfg, SemanticFlags, ses_method};
use swc_atoms::Atom;
use swc_common::{EqIgnoreSpan, Spanned, SyntaxContext};
use swc_ecma_ast::{BinaryOp, Bool, Expr, Number, Str, UnaryOp, op};
use swc_ecma_utils::{ExprCtx, ExprExt, Value};
pub use swc_tac::{Item, ItemGetter};
use swc_tac::{ItemGetterExt, PropKey, PropVal, SpreadOr};
pub type _Ident = Ident;
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
    pub fn simplify_loads(&mut self) {
        for (k, kd) in self.blocks.iter() {
            let mut m = BTreeMap::new();
            for s in kd.stmts.iter().cloned() {
                let x = &mut self.values[s];
                if let SValueW {
                    value: SValue::LoadId(i),
                } = x
                {
                    if let Some(g) = m.get(&*i) {
                        *x = SValueW {
                            value: SValue::Item {
                                item: Item::Just { id: *g },
                                span: None,
                            },
                        }
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
        let mut redo = true;
        while take(&mut redo) {
            for ref_ in self.values.iter().map(|a| a.0).collect::<BTreeSet<_>>() {
                redo = redo | self.simplify_just(ref_);
            }
        }
    }
}
pub trait SValGetter<I: Copy, B, F = SFunc>: ItemGetter<I, F> {
    fn val(&self, id: I) -> Option<&SValue<I, B, F>>;
    fn val_mut(&mut self, id: I) -> Option<&mut SValue<I, B, F>>;
    fn inputs<'a>(&'a self, block: B, param: usize) -> Box<dyn Iterator<Item = I> + 'a>
    where
        I: 'a,
        B: 'a,
    {
        Box::new(empty())
    }
    fn input<'a>(&'a self, block: B, param: usize) -> Option<I>
    where
        I: Eq + 'a,
        B: 'a,
    {
        let mut i = self.inputs(block, param);
        let n = i.next()?;
        for o in i {
            if o != n {
                return None;
            }
        }
        Some(n)
    }
    fn taints_object(&self, id: I) -> bool {
        return true;
    }
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
#[doc(hidden)]
pub fn _get_ident<'a, I: Copy, B, F>(
    a: &'a (dyn SValGetter<I, B, F> + 'a),
    mut i: I,
) -> Option<Ident> {
    let mut bak = None;
    loop {
        match a.val(i)? {
            SValue::Param { block, idx, ty } => return bak,
            SValue::Item { item, span } => match item {
                Item::Just { id } => {
                    i = *id;
                }
                _ => return bak,
            },
            SValue::Assign { target, val } => {
                i = *val;
            }
            SValue::LoadId(a) => return Some(a.clone()),
            SValue::StoreId { target, val } => {
                bak = Some(target.clone());
                i = *val;
            }
            SValue::EdgeBlocker { value, span } => {
                i = *value;
            }
        }
    }
}
#[doc(hidden)]
pub fn _get_item_mut<'a, 'b: 'a, I: Copy, B, F>(
    a: &'b mut (dyn SValGetter<I, B, F> + 'a),
    mut i: I,
) -> Option<&'a mut Item<I, F>> {
    let a: *mut (dyn SValGetter<I, B, F> + 'a) = a as *mut _;
    loop {
        //SAFETY: only borrowed once; values are moved before continuing the loop
        match unsafe { &mut *a }.val_mut(i)? {
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
            fn get_mut_item(&mut self, i: I) -> Option<&mut $crate::simplify::Item<I, F>>{
                $crate::simplify::_get_item_mut(self,i)
            }
            fn get_ident(&self, i: I) -> Option<$crate::simplify::_Ident>{
                $crate::simplify::_get_ident(self,i)
            }
        }
    };
}
impl SValGetter<Id<SValueW>, Id<SBlock>> for SCfg {
    fn val(&self, id: Id<SValueW>) -> Option<&SValue<Id<SValueW>, Id<SBlock>>> {
        Some(&self.values[id].value)
    }
    fn val_mut(&mut self, id: Id<SValueW>) -> Option<&mut SValue<Id<SValueW>, Id<SBlock>, SFunc>> {
        Some(&mut self.values[id].value)
    }
    fn inputs<'a>(
        &'a self,
        block: Id<SBlock>,
        param: usize,
    ) -> Box<dyn Iterator<Item = Id<SValueW>> + 'a>
    where
        Id<SValueW>: 'a,
        Id<SBlock>: 'a,
    {
        Box::new(SCfg::inputs(self, block, param))
    }
    fn taints_object(&self, id: Id<SValueW>) -> bool {
        SCfg::taints_object(self, &id)
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
impl<I: Copy + Eq, B: Clone, F> SValue<I, B, F> {
    pub fn array_in(
        &self,
        semantics: &SemanticCfg,
        k: &(dyn SValGetter<I, B, F> + '_),
        pierce: bool,
    ) -> Option<Vec<SpreadOr<I>>> {
        match self {
            SValue::Param { block, idx, ty } if pierce => {
                let mut i = k
                    .inputs(block.clone(), *idx)
                    .filter_map(|i| k.val(i))
                    .filter_map(|t| t.array_in(semantics, k, pierce));
                let mut n = i.next()?;
                for j in i {
                    if j != n {
                        return None;
                    }
                }
                Some(n)
            }
            SValue::Item { item, span } => {
                match item {
                    Item::Arr { members } => Some(members.clone()),
                    Item::Mem { obj, mem } => {
                        match k.val(*mem).and_then(|m| m.const_in(semantics, k, pierce)) {
                            Some(Lit::Num(n)) => match k.val(*obj) {
                                Some(i)
                                    if semantics
                                        .flags
                                        .contains(SemanticFlags::NO_MONKEYPATCHING) =>
                                {
                                    match i.array_in(semantics, k, pierce) {
                                        None => None,
                                        Some(a) => {
                                            if a.iter().any(|SpreadOr { value: _, is_spread: v }| *v) {
                                            return None;
                                        };
                                            a
                                        .get((n.value.round() as usize))
                                        .and_then(|SpreadOr { value: a, is_spread: _ }| k.val(*a))
                                        .and_then(|a| a.array_in(semantics, k, pierce))
                                        }
                                    }
                                }
                                _ => None,
                            },
                            _ => None,
                        }
                    }
                    Item::Call { callee, args }
                        if semantics.flags.contains(SemanticFlags::NO_MONKEYPATCHING) =>
                    {
                        match callee {
                            TCallee::Member { func, member } => {
                                let member = k.val(*member)?.const_in(semantics, k, pierce)?;
                                let Lit::Str(s) = member else {
                                    return None;
                                };
                                let func = k.val(*func)?;
                                match func.array_in(semantics, k, pierce) {
                                    Some(members) => match s.value.as_str()? {
                                        "concat" => {
                                            let mut members: Vec<SpreadOr<I>> = members;
                                            for SpreadOr {
                                                value: a,
                                                is_spread: s,
                                            } in args.iter().cloned()
                                            {
                                                let a = k.val(a)?;
                                                let i = a.array_in(semantics, k, pierce)?;
                                                if s {
                                                    return None;
                                                } else {
                                                    members.extend(i);
                                                }
                                            }
                                            Some(members)
                                        }
                                        "slice" => {
                                            let begin: Option<usize> = args
                                            .get(0)
                                            .cloned().and_then(|SpreadOr { value: a, is_spread: b }|(!b).then(move||a))
                                            .and_then(|a| k.val(a))
                                            .and_then(|v| v.const_in(semantics, k, pierce))
                                            .and_then(|v| v.as_num().map(|a| a.value as usize));
                                            let end: Option<usize> = args
                                            .get(1)
                                            .cloned().and_then(|SpreadOr { value: a, is_spread: b }|(!b).then(move||a))
                                            .and_then(|a| k.val(a))
                                            .and_then(|v| v.const_in(semantics, k, pierce))
                                            .and_then(|v| v.as_num().map(|a| a.value as usize));
                                            let mut members: Vec<SpreadOr<I>> = members;
                                            if members.iter().any(|SpreadOr { value: _, is_spread: v }| *v) {
                                            return None;
                                        }
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
                }
            }
            _ => None,
        }
    }
    pub fn const_in(
        &self,
        semantics: &SemanticCfg,
        k: &(dyn SValGetter<I, B, F> + '_),
        pierce: bool,
    ) -> Option<Lit> {
        match self {
            SValue::Param { block, idx, ty } if pierce => {
                let mut i = k.inputs(block.clone(), *idx).filter_map(|i| k.val(i));
                let mut n = i.next()?.const_in(semantics, k, pierce)?;
                for j in i {
                    let j = j.const_in(semantics, k, pierce)?;
                    if j != n {
                        return None;
                    }
                }
                Some(n)
            }
            SValue::Item { item, span } => match item {
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
                    let left = k.val(*l2)?;
                    let right = k.val(*r2)?;
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
                                let left = left.const_in(semantics, k, pierce)?;
                                let right = right.const_in(semantics, k, pierce)?;
                                (left, right)
                            }
                        },
                        (left_val, right_val) => {
                            let left = left_val.const_in(semantics, k, pierce);
                            let right = right_val.const_in(semantics, k, pierce);
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
                                (_, r, Some(l), _)
                                    if *op == op!("in")
                                        && pierce
                                        && (!k.taints_object(*r2)
                                            || semantics
                                                .flags
                                                .contains(SemanticFlags::ALL_OBJECTS_FROZEN)) =>
                                {
                                    match r {
                                        SValue::Item {
                                            item: Item::Obj { members },
                                            span,
                                        } => match {
                                            // let l = k.val(*mem).and_then(|m| m.const_in(semantics, k, pierce))?;
                                            let mut i = members.iter();
                                            loop {
                                                let Some(i) = i.next() else {
                                                    break Some(false);
                                                };
                                                let l2 = match &i.0 {
                                                    PropKey::Lit(l) => Lit::Str(Str {
                                                        span: span
                                                            .clone()
                                                            .unwrap_or(Span::dummy_with_cmt()),
                                                        value: l.0.clone().into(),
                                                        raw: None,
                                                    }),
                                                    PropKey::Computed(c) => {
                                                        match k.val(*c).and_then(|w| {
                                                            w.const_in(semantics, k, pierce)
                                                        }) {
                                                            None => return None,
                                                            Some(l) => l,
                                                        }
                                                    }
                                                    _ => break None,
                                                };
                                                if l2 != *l {
                                                    continue;
                                                };
                                                break Some(true);
                                            }
                                        } {
                                            Some(v) => {
                                                return Some(Lit::Bool(Bool {
                                                    span: span
                                                        .clone()
                                                        .unwrap_or(Span::dummy_with_cmt()),
                                                    value: v,
                                                }));
                                            }
                                            None => (left?, right?),
                                        },
                                        _ => (left?, right?),
                                    }
                                }
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
                    let l = k.val(*arg)?.const_in(semantics, k, pierce)?;
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
                    match k.val(*obj) {
                        Some(SValue::Item {
                            item: Item::Obj { members },
                            span,
                        }) => match {
                            let l = k.val(*mem).and_then(|m| m.const_in(semantics, k, pierce))?;
                            let mut i = members.iter();
                            loop {
                                let Some(i) = i.next() else {
                                    break None;
                                };
                                let l2 = match &i.0 {
                                    PropKey::Lit(l) => Lit::Str(Str {
                                        span: span.clone().unwrap_or(Span::dummy_with_cmt()),
                                        value: l.0.clone().into(),
                                        raw: None,
                                    }),
                                    PropKey::Computed(c) => {
                                        match k
                                            .val(*c)
                                            .and_then(|w| w.const_in(semantics, k, pierce))
                                        {
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
                                return k.val(v).and_then(|w| w.const_in(semantics, k, pierce));
                            }
                            None => {}
                        },
                        _ => {}
                    }
                    match k.val(*mem).and_then(|m| m.const_in(semantics, k, pierce)) {
                        Some(Lit::Str(s)) => match s.value.as_str()? {
                            "length" => match k.val(*obj) {
                                Some(i)
                                    if semantics
                                        .flags
                                        .contains(SemanticFlags::NO_MONKEYPATCHING) =>
                                {
                                    match i.array_in(semantics, k, pierce) {
                                        None => {
                                            let l = i.const_in(semantics, k, pierce)?;
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
                        Some(Lit::Num(n)) => {
                            match k.val(*obj) {
                                Some(i)
                                    if semantics
                                        .flags
                                        .contains(SemanticFlags::NO_MONKEYPATCHING) =>
                                {
                                    match i.array_in(semantics, k, pierce) {
                                    None => None,
                                    Some(a) => a
                                        .iter()
                                        .all(|SpreadOr { value: _, is_spread: v }| !*v)
                                        .then(|| {
                                            a.get((n.value.round() as usize))
                                                .and_then(|SpreadOr { value: a, is_spread: _ }| k.val(*a))
                                                .and_then(|a| a.const_in(semantics, k, pierce))
                                        })
                                        .flatten(),
                                }
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                }
                Item::Call { callee, args }
                    if semantics.flags.contains(SemanticFlags::NO_MONKEYPATCHING) =>
                {
                    match callee {
                        TCallee::Member { func, member } => {
                            let member = k.val(*member)?.const_in(semantics, k, pierce)?;
                            let Lit::Str(s) = member else {
                                return None;
                            };
                            let func = k.val(*func)?;
                            match func {
                                _ => {
                                    let func = func.const_in(semantics, k, pierce)?;
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
                                                    let i = k
                                                        .val(*n)?
                                                        .const_in(semantics, k, pierce)?;
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
