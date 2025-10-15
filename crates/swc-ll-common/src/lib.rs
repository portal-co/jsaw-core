use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::convert::Infallible;
use std::iter::{empty, once};
use std::mem::take;
use std::sync::Arc;

use anyhow::Context;
use arena_traits::IndexAlloc;
use bitflags::bitflags;
use either::Either;
use id_arena::{Arena, Id};
// use lam::LAM;
use linearize::{StaticMap, static_map};
use portal_jsc_common::{natives::Native, syntax::Asm};
use portal_jsc_swc_util::brighten::Purity;
use portal_jsc_swc_util::{ImportMapper, ResolveNatives, SemanticCfg, SemanticFlags, ses_method};
use portal_solutions_swibb::ConstCollector;
use ssa_impls::dom::{dominates, domtree};
use swc_atoms::Atom;
use swc_cfg::{Block, Catch, Cfg, Func};
use swc_common::{EqIgnoreSpan, Mark, Span, Spanned, SyntaxContext};
use swc_ecma_ast::{
    AssignExpr, AssignOp, AssignTarget, BinaryOp, Bool, Callee, Class, ClassMember,
    ComputedPropName, CondExpr, Expr, Function, Lit, MemberExpr, MemberProp, MetaPropKind, Number,
    Param, Pat, SimpleAssignTarget, Stmt, Str, TsType, TsTypeAnn, TsTypeParamDecl, UnaryOp,
};

use swc_ecma_ast::Id as Ident;
bitflags! {
    #[repr(transparent)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
    pub struct MemberFlags: u64{
        const STATIC = 0x1;
        const PRIVATE = 0x2;
    }
}
pub trait ItemGetter<I, F> {
    fn get_item(&self, i: I) -> Option<&Item<I, F>>;
    fn get_mut_item(&mut self, i: I) -> Option<&mut Item<I, F>>;
    fn get_ident(&self, i: I) -> Option<Ident>;
}

pub trait ItemGetterExt<I, F>: ItemGetter<I, F> {
    fn native_of(&self, mut i: I) -> Option<Native<I>>
    where
        I: Clone,
    {
        loop {
            let g = self.get_item(i)?;
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
                if let Some(i) = self.get_ident(func.clone()) {
                    if i.0 == "globalThis" {
                        break;
                    }
                }
                let Item::Just { id } = self.get_item(func.clone())? else {
                    return None;
                };
                func = id;
            }
            let n = loop {
                let id = match self.get_item(member.clone())? {
                    Item::Lit { lit: Lit::Str(s) } => {
                        if let Some(m) = s.value.strip_prefix("~Natives_") {
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
    fn inlinable(&self, d: &Item<I, F>) -> bool
    where
        I: Clone,
    {
        let tcfg = self;
        match d {
            Item::Just { id } => tcfg.get_item(id.clone()).is_some(),
            Item::Asm { value }
                if match value {
                    Asm::OrZero(value) => tcfg.get_item(value.clone()).is_some(),
                    _ => todo!(),
                } =>
            {
                true
            }
            Item::Lit { lit } => true,
            Item::Un { arg, op }
                if !matches!(op, UnaryOp::Delete) && tcfg.get_item(arg.clone()).is_some() =>
            {
                true
            }
            _ => false,
        }
    }
    fn simplify_just(&mut self, i: I) -> bool
    where
        Item<I, F>: Clone,
        I: Clone,
    {
        if let Some(g) = self.get_item(i.clone()).and_then(|j| match j {
            Item::Just { id } => self.get_item(id.clone()),
            _ => None,
        }) {
            if self.inlinable(g) {
                let g = g.clone();
                if let Some(h) = self.get_mut_item(i) {
                    *h = g;
                    return true;
                }
            }
        }
        return false;
    }
}
impl<T: ItemGetter<I, F> + ?Sized, I, F> ItemGetterExt<I, F> for T {}

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Private {
    pub sym: Atom,
    pub ctxt: SyntaxContext,
    pub span: Span,
}
#[derive(Clone, Ord, PartialEq, PartialOrd, Eq, Debug)]
#[non_exhaustive]
pub enum PropKey<I> {
    Lit(Ident),
    Computed(I),
}

impl<I> PropKey<I> {
    pub fn as_ref(&self) -> PropKey<&I> {
        match self {
            PropKey::Lit(a) => PropKey::Lit(a.clone()),
            PropKey::Computed(c) => PropKey::Computed(c),
        }
    }
    pub fn as_mut(&mut self) -> PropKey<&mut I> {
        match self {
            PropKey::Lit(a) => PropKey::Lit(a.clone()),
            PropKey::Computed(c) => PropKey::Computed(c),
        }
    }
    pub fn map<J, E>(self, f: &mut (dyn FnMut(I) -> Result<J, E> + '_)) -> Result<PropKey<J>, E> {
        Ok(match self {
            PropKey::Lit(l) => PropKey::Lit(l),
            PropKey::Computed(x) => PropKey::Computed(f(x)?),
        })
    }
}
#[derive(Clone, Ord, PartialEq, PartialOrd, Eq, Debug)]
#[non_exhaustive]
pub enum PropVal<I, F> {
    Item(I),
    Getter(F),
    Setter(F),
    Method(F),
}
impl<I, F> PropVal<I, F> {
    pub fn as_ref(&self) -> PropVal<&I, &F> {
        match self {
            PropVal::Item(a) => PropVal::Item(a),
            PropVal::Getter(f) => PropVal::Getter(f),
            PropVal::Setter(f) => PropVal::Setter(f),
            PropVal::Method(f) => PropVal::Method(f),
        }
    }
    pub fn as_mut(&mut self) -> PropVal<&mut I, &mut F> {
        match self {
            PropVal::Item(a) => PropVal::Item(a),
            PropVal::Getter(f) => PropVal::Getter(f),
            PropVal::Setter(f) => PropVal::Setter(f),
            PropVal::Method(f) => PropVal::Method(f),
        }
    }
    pub fn map<I2, F2, Cx: ?Sized, E>(
        self,
        cx: &mut Cx,
        i: &mut (dyn FnMut(&mut Cx, I) -> Result<I2, E> + '_),
        f: &mut (dyn FnMut(&mut Cx, F) -> Result<F2, E> + '_),
    ) -> Result<PropVal<I2, F2>, E> {
        Ok(match self {
            PropVal::Item(a) => PropVal::Item(i(cx, a)?),
            PropVal::Getter(a) => PropVal::Getter(f(cx, a)?),
            PropVal::Setter(a) => PropVal::Setter(f(cx, a)?),
            PropVal::Method(a) => PropVal::Method(f(cx, a)?),
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TCallee<I> {
    Val(I),
    Member { func: I, member: I },
    PrivateMember { func: I, member: Private },
    Import,
    Super,
    Eval,
    // Static(Ident),
}
impl<I> TCallee<I> {
    pub fn as_ref(&self) -> TCallee<&I> {
        match self {
            TCallee::Val(a) => TCallee::Val(a),
            TCallee::Member { func: r#fn, member } => TCallee::Member { func: r#fn, member },
            TCallee::PrivateMember { func: r#fn, member } => TCallee::PrivateMember {
                func: r#fn,
                member: member.clone(),
            },
            TCallee::Import => TCallee::Import,
            TCallee::Super => TCallee::Super,
            TCallee::Eval => TCallee::Eval,
            // TCallee::Static(a) => TCallee::Static(a.clone()),
        }
    }
    pub fn as_mut(&mut self) -> TCallee<&mut I> {
        match self {
            TCallee::Val(a) => TCallee::Val(a),
            TCallee::Member { func: r#fn, member } => TCallee::Member { func: r#fn, member },
            TCallee::PrivateMember { func: r#fn, member } => TCallee::PrivateMember {
                func: r#fn,
                member: member.clone(),
            },
            TCallee::Import => TCallee::Import,
            TCallee::Super => TCallee::Super,
            TCallee::Eval => TCallee::Eval,
            // TCallee::Static(a) => TCallee::Static(a.clone()),
        }
    }
    pub fn map<J, E>(self, f: &mut impl FnMut(I) -> Result<J, E>) -> Result<TCallee<J>, E> {
        Ok(match self {
            TCallee::Val(a) => TCallee::Val(f(a)?),
            TCallee::Member { func: r#fn, member } => TCallee::Member {
                func: f(r#fn)?,
                member: f(member)?,
            },
            TCallee::PrivateMember { func: r#fn, member } => TCallee::PrivateMember {
                func: f(r#fn)?,
                member,
            },
            TCallee::Import => TCallee::Import,
            TCallee::Super => TCallee::Super,
            TCallee::Eval => TCallee::Eval,
            // TCallee::Static(a) => TCallee::Static(a),
        })
    }
}
impl<I: PartialEq, F> Item<I, F> {
    pub fn will_ruin(&self, i: &I) -> bool {
        match self {
            Item::Mem { obj, mem } => mem == i,
            Item::Call {
                callee: TCallee::Eval,
                args,
            } => true,
            a => a.refs().any(|r| r == i),
        }
    }
}
impl<I, F> Item<I, F> {
    pub fn nothrow(&self) -> bool {
        match self {
            Item::Arguments
            | Item::This
            | Item::Undef
            | Item::Meta { .. }
            | Item::Just { .. }
            | Item::Lit { .. } => true,
            Item::Un {
                op: UnaryOp::Void | UnaryOp::TypeOf,
                ..
            } => true,
            _ => false,
        }
    }
    pub fn will_store(&self, i: &Ident) -> bool {
        match self {
            Item::Call {
                callee: TCallee::Eval,
                args,
            } => true,
            _ => false,
        }
    }
}
impl<I: Eq, F> Item<I, F> {
    pub fn taints_object(&self, a: &I) -> bool {
        match self {
            Item::Call { callee, args } => {
                matches!(callee, TCallee::Eval)
                    || args.iter().any(
                        |SpreadOr {
                             value: b,
                             is_spread: _,
                         }| b == a,
                    )
            }
            _ => false,
        }
    }
}
pub fn inlinable<I: Clone, F>(d: &Item<I, F>, tcfg: &(dyn ItemGetter<I, F> + '_)) -> bool {
    tcfg.inlinable(d)
}
#[derive(Clone, Debug, PartialEq, Eq, Copy, PartialOrd, Ord)]
pub struct SpreadOr<I> {
    pub value: I,
    pub is_spread: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Item<I, F> {
    Just {
        id: I,
    },
    Bin {
        left: I,
        right: I,
        op: BinaryOp,
    },
    Un {
        arg: I,
        op: UnaryOp,
    },
    Mem {
        obj: I,
        mem: I,
    },
    PrivateMem {
        obj: I,
        mem: Private,
    },
    HasPrivateMem {
        obj: I,
        mem: Private,
    },
    Func {
        func: F,
        arrow: bool,
    },
    Lit {
        lit: Lit,
    },
    Call {
        callee: TCallee<I>,
        args: Vec<SpreadOr<I>>,
    },
    New {
        class: I,
        args: Vec<I>,
    },
    Obj {
        members: Vec<(PropKey<I>, PropVal<I, F>)>,
    },
    Class {
        superclass: Option<I>,
        members: Vec<(MemberFlags, PropKey<I>, PropVal<Option<I>, F>)>,
        constructor: Option<F>,
    },
    Arr {
        members: Vec<SpreadOr<I>>,
    },
    StaticSubArray {
        begin: usize,
        end: usize,
        wrapped: I,
    },
    StaticSubObject {
        wrapped: I,
        keys: Vec<PropKey<I>>,
    },
    Yield {
        value: Option<I>,
        delegate: bool,
    },
    Await {
        value: I,
    },
    Asm {
        value: Asm<I>,
    },
    Undef,
    This,
    Select {
        cond: I,
        then: I,
        otherwise: I,
    },
    Arguments,
    Meta {
        prop: MetaPropKind,
    }, // Intrinsic {
       //     value: Native<I>,
       // },
}
impl<I, F> Item<I, F> {
    pub fn map<J, E>(self, f: &mut (dyn FnMut(I) -> Result<J, E> + '_)) -> Result<Item<J, F>, E> {
        self.map2(f, &mut |a, b| a(b), &mut |_, b| Ok(b))
    }
}
impl<I, F> Item<I, F> {
    pub fn as_ref(&self) -> Item<&I, &F> {
        match self {
            Item::Just { id } => Item::Just { id },
            Item::Bin { left, right, op } => Item::Bin {
                left,
                right,
                op: *op,
            },
            Item::Un { arg, op } => Item::Un { arg, op: *op },
            Item::Mem { obj, mem } => Item::Mem { obj, mem },
            Item::PrivateMem { obj, mem } => Item::PrivateMem {
                obj,
                mem: mem.clone(),
            },
            Item::HasPrivateMem { obj, mem } => Item::HasPrivateMem {
                obj,
                mem: mem.clone(),
            },
            Item::Func { func, arrow } => Item::Func {
                func,
                arrow: *arrow,
            },
            Item::Lit { lit } => Item::Lit { lit: lit.clone() },
            Item::Call { callee, args } => Item::Call {
                callee: callee.as_ref(),
                args: args
                    .iter()
                    .map(
                        |SpreadOr {
                             value: a,
                             is_spread: b,
                         }| SpreadOr {
                            value: a,
                            is_spread: *b,
                        },
                    )
                    .collect(),
            },
            Item::New { class, args } => Item::New {
                class,
                args: args.iter().collect(),
            },
            Item::Obj { members } => Item::Obj {
                members: members
                    .iter()
                    .map(|(a, b)| (a.as_ref(), b.as_ref()))
                    .collect(),
            },
            Item::Arr { members } => Item::Arr {
                members: members
                    .iter()
                    .map(
                        |SpreadOr {
                             value: a,
                             is_spread: b,
                         }| SpreadOr {
                            value: a,
                            is_spread: *b,
                        },
                    )
                    .collect(),
            },
            Item::Yield { value, delegate } => Item::Yield {
                value: value.as_ref(),
                delegate: *delegate,
            },
            Item::Await { value } => Item::Await { value },
            Item::Asm { value } => Item::Asm {
                value: value.as_ref(),
            },
            Item::Undef => Item::Undef,
            Item::This => Item::This,
            Item::Arguments => Item::Arguments,
            Item::Class {
                superclass,
                members,
                constructor,
            } => Item::Class {
                superclass: superclass.as_ref(),
                constructor: constructor.as_ref(),
                members: members
                    .iter()
                    .map(|(a, b, c)| {
                        (
                            *a,
                            b.as_ref(),
                            c.as_ref()
                                .map(
                                    &mut (),
                                    &mut |cx, a: &Option<I>| Ok::<_, Infallible>(a.as_ref()),
                                    &mut |cx, b| Ok(b),
                                )
                                .unwrap(),
                        )
                    })
                    .collect(),
            },
            Item::Select {
                cond,
                then,
                otherwise,
            } => Item::Select {
                cond,
                then,
                otherwise,
            },
            Item::StaticSubArray {
                begin,
                end,
                wrapped,
            } => Item::StaticSubArray {
                begin: *begin,
                end: *end,
                wrapped,
            },
            Item::StaticSubObject { wrapped, keys } => Item::StaticSubObject {
                wrapped,
                keys: keys.iter().map(|a| a.as_ref()).collect(),
            },
            Item::Meta { prop } => Item::Meta { prop: *prop },
        }
    }
    pub fn as_mut(&mut self) -> Item<&mut I, &mut F> {
        match self {
            Item::Meta { prop } => Item::Meta { prop: *prop },
            Item::Select {
                cond,
                then,
                otherwise,
            } => Item::Select {
                cond,
                then,
                otherwise,
            },
            Item::Just { id } => Item::Just { id },
            Item::Bin { left, right, op } => Item::Bin {
                left,
                right,
                op: *op,
            },
            Item::Un { arg, op } => Item::Un { arg, op: *op },
            Item::Mem { obj, mem } => Item::Mem { obj, mem },
            Item::PrivateMem { obj, mem } => Item::PrivateMem {
                obj,
                mem: mem.clone(),
            },
            Item::HasPrivateMem { obj, mem } => Item::HasPrivateMem {
                obj,
                mem: mem.clone(),
            },
            Item::Func { func, arrow } => Item::Func {
                func,
                arrow: *arrow,
            },
            Item::Lit { lit } => Item::Lit { lit: lit.clone() },
            Item::Call { callee, args } => Item::Call {
                callee: callee.as_mut(),
                args: args
                    .iter_mut()
                    .map(
                        |SpreadOr {
                             value: a,
                             is_spread: b,
                         }| SpreadOr {
                            value: a,
                            is_spread: *b,
                        },
                    )
                    .collect(),
            },
            Item::New { class, args } => Item::New {
                class,
                args: args.iter_mut().collect(),
            },
            Item::Obj { members } => Item::Obj {
                members: members
                    .iter_mut()
                    .map(|(a, b)| (a.as_mut(), b.as_mut()))
                    .collect(),
            },
            Item::Arr { members } => Item::Arr {
                members: members
                    .iter_mut()
                    .map(
                        |SpreadOr {
                             value: a,
                             is_spread: b,
                         }| SpreadOr {
                            value: a,
                            is_spread: *b,
                        },
                    )
                    .collect(),
            },
            Item::Yield { value, delegate } => Item::Yield {
                value: value.as_mut(),
                delegate: *delegate,
            },
            Item::Await { value } => Item::Await { value },
            Item::Asm { value } => Item::Asm {
                value: value.as_mut(),
            },
            Item::Undef => Item::Undef,
            Item::This => Item::This,
            Item::Arguments => Item::Arguments,
            Item::Class {
                superclass,
                members,
                constructor,
            } => Item::Class {
                superclass: superclass.as_mut(),
                constructor: constructor.as_mut(),
                members: members
                    .iter_mut()
                    .map(|(a, b, c)| {
                        (
                            *a,
                            b.as_mut(),
                            c.as_mut()
                                .map(
                                    &mut (),
                                    &mut |cx, a| Ok::<_, Infallible>(a.as_mut()),
                                    &mut |cx, b| Ok(b),
                                )
                                .unwrap(),
                        )
                    })
                    .collect(),
            },
            Item::StaticSubArray {
                begin,
                end,
                wrapped,
            } => Item::StaticSubArray {
                begin: *begin,
                end: *end,
                wrapped,
            },
            Item::StaticSubObject { wrapped, keys } => Item::StaticSubObject {
                wrapped,
                keys: keys.iter_mut().map(|a| a.as_mut()).collect(),
            }, // Item::Intrinsic { value } => Item::Intrinsic {
               //     value: value.as_mut(),
               // },
        }
    }
    pub fn map2<J, G, E, C: ?Sized>(
        self,
        cx: &mut C,
        f: &mut (dyn FnMut(&mut C, I) -> Result<J, E> + '_),
        g: &mut (dyn FnMut(&mut C, F) -> Result<G, E> + '_),
    ) -> Result<Item<J, G>, E> {
        Ok(match self {
            Item::Meta { prop } => Item::Meta { prop },
            Item::Select {
                cond,
                then,
                otherwise,
            } => Item::Select {
                cond: f(cx, cond)?,
                then: f(cx, then)?,
                otherwise: f(cx, otherwise)?,
            },
            Item::Just { id } => Item::Just { id: f(cx, id)? },
            Item::Bin { left, right, op } => Item::Bin {
                left: f(cx, left)?,
                right: f(cx, right)?,
                op,
            },
            Item::Un { arg, op } => Item::Un {
                arg: f(cx, arg)?,
                op,
            },
            Item::Mem { obj, mem } => Item::Mem {
                obj: f(cx, obj)?,
                mem: f(cx, mem)?,
            },
            Item::PrivateMem { obj, mem } => Item::PrivateMem {
                obj: f(cx, obj)?,
                mem,
            },
            Item::HasPrivateMem { obj, mem } => Item::HasPrivateMem {
                obj: f(cx, obj)?,
                mem,
            },
            Item::Func { func, arrow } => Item::Func {
                func: g(cx, func)?,
                arrow,
            },
            Item::Lit { lit } => Item::Lit { lit },
            Item::Call { callee, args } => Item::Call {
                callee: callee.map(&mut |a| f(cx, a))?,
                args: args
                    .into_iter()
                    .map(
                        |SpreadOr {
                             value: a,
                             is_spread: b,
                         }| {
                            f(cx, a).map(|c| SpreadOr {
                                value: c,
                                is_spread: b,
                            })
                        },
                    )
                    .collect::<Result<Vec<_>, E>>()?,
            },
            Item::New { class, args } => Item::New {
                class: f(cx, class)?,
                args: args
                    .into_iter()
                    .map(|a| f(cx, a))
                    .collect::<Result<Vec<J>, E>>()?,
            },
            Item::Obj { members } => Item::Obj {
                members: members
                    .into_iter()
                    .map(|(a, b)| Ok((a.map(&mut |a| f(cx, a))?, b.map(cx, f, g)?)))
                    .collect::<Result<_, E>>()?,
            },
            Item::Arr { members } => Item::Arr {
                members: members
                    .into_iter()
                    .map(
                        |SpreadOr {
                             value: a,
                             is_spread: b,
                         }| {
                            f(cx, a).map(|c| SpreadOr {
                                value: c,
                                is_spread: b,
                            })
                        },
                    )
                    .collect::<Result<_, E>>()?,
            },
            Item::Yield { value, delegate } => Item::Yield {
                value: match value {
                    None => None,
                    Some(a) => Some(f(cx, a)?),
                },
                delegate: delegate,
            },
            Item::Await { value } => Item::Await {
                value: f(cx, value)?,
            },
            Item::Undef => Item::Undef,
            Item::Arguments => Item::Arguments,
            Item::Asm { value } => Item::Asm {
                value: value.map(&mut |a| f(cx, a))?,
            },
            Item::This => Item::This,
            Item::Class {
                superclass,
                members,
                constructor,
            } => Item::Class {
                superclass: match superclass {
                    None => None,
                    Some(a) => Some(f(cx, a)?),
                },
                constructor: match constructor {
                    None => None,
                    Some(a) => Some(g(cx, a)?),
                },
                members: members
                    .into_iter()
                    .map(|(a, b, c)| {
                        Ok((
                            a,
                            b.map(&mut |a| f(cx, a))?,
                            c.map(
                                cx,
                                &mut |cx, a: Option<I>| {
                                    Ok(match a {
                                        None => None,
                                        Some(v) => Some(f(cx, v)?),
                                    })
                                },
                                g,
                            )?,
                        ))
                    })
                    .collect::<Result<_, E>>()?,
            },
            Item::StaticSubArray {
                begin,
                end,
                wrapped,
            } => Item::StaticSubArray {
                begin,
                end,
                wrapped: f(cx, wrapped)?,
            },
            Item::StaticSubObject { wrapped, keys } => Item::StaticSubObject {
                wrapped: f(cx, wrapped)?,
                keys: keys
                    .into_iter()
                    .map(|k| k.map(&mut |i| f(cx, i)))
                    .collect::<Result<_, E>>()?,
            }, // Item::Intrinsic { value } => Item::Intrinsic {
               //     value: value.map(&mut |a| f(cx, a))?,
               // },
        })
    }
    pub fn funcs<'a>(&'a self) -> Box<dyn Iterator<Item = &'a F> + 'a> {
        match self {
            Item::Func { func, arrow } => Box::new(once(func)),
            Item::Obj { members } => Box::new(members.iter().filter_map(|m| match &m.1 {
                PropVal::Getter(f) | PropVal::Setter(f) | PropVal::Method(f) => Some(f),
                _ => None,
            })),
            Item::Class {
                superclass,
                members,
                constructor,
            } => Box::new(
                members
                    .iter()
                    .filter_map(|m| match &m.2 {
                        PropVal::Getter(f) | PropVal::Setter(f) | PropVal::Method(f) => Some(f),
                        _ => None,
                    })
                    .chain(constructor.iter()),
            ),
            _ => Box::new(empty()),
        }
    }
    pub fn refs<'a>(&'a self) -> Box<dyn Iterator<Item = &'a I> + 'a> {
        use crate as swc_tac;
        match self {
            swc_tac::Item::Just { id } => Box::new(once(id)),
            swc_tac::Item::Bin { left, right, op } => Box::new([left, right].into_iter()),
            swc_tac::Item::Un { arg, op } => Box::new(once(arg)),
            swc_tac::Item::Mem { obj, mem } => Box::new([obj, mem].into_iter()),
            Item::PrivateMem { obj, mem } | Item::HasPrivateMem { obj, mem } => Box::new(once(obj)),
            swc_tac::Item::Func { func, arrow } => Box::new(empty()),
            swc_tac::Item::Lit { lit } => Box::new(empty()),
            swc_tac::Item::Call { callee, args } => Box::new(
                match callee {
                    swc_tac::TCallee::Val(a) | TCallee::PrivateMember { func: a, member: _ } => {
                        vec![a]
                    }
                    swc_tac::TCallee::Member { func: r#fn, member } => vec![r#fn, member],
                    TCallee::Import | TCallee::Super | TCallee::Eval => vec![], // swc_tac::TCallee::Static(_) => vec![],
                }
                .into_iter()
                .chain(args.iter().map(
                    |SpreadOr {
                         value: a,
                         is_spread: _,
                     }| a,
                )),
            ),
            Item::New { class, args } => Box::new(args.iter().chain([class])),
            swc_tac::Item::Obj { members } => Box::new(members.iter().flat_map(|m| {
                let v: Box<dyn Iterator<Item = &I> + '_> = match &m.1 {
                    PropVal::Getter(a) | PropVal::Setter(a) | PropVal::Method(a) => {
                        Box::new(empty())
                    }
                    PropVal::Item(i) => Box::new(once(i)),
                };
                let w: Box<dyn Iterator<Item = &I> + '_> = match &m.0 {
                    swc_tac::PropKey::Lit(_) => Box::new(empty()),
                    swc_tac::PropKey::Computed(c) => Box::new(once(c)),
                };
                v.chain(w)
            })),
            swc_tac::Item::Arr { members } => Box::new(members.iter().map(
                |SpreadOr {
                     value: a,
                     is_spread: _,
                 }| a,
            )),
            swc_tac::Item::Yield { value, delegate } => Box::new(value.iter()),
            swc_tac::Item::Await { value } => Box::new(once(value)),
            swc_tac::Item::Undef | Item::This | Item::Arguments | Item::Meta { .. } => {
                Box::new(empty())
            }
            Item::Asm { value } => Box::new(value.refs()),
            Item::Class {
                superclass,
                members,
                constructor,
            } => Box::new(superclass.iter().chain(members.iter().flat_map(|m| {
                let v: Box<dyn Iterator<Item = &I> + '_> = match &m.2 {
                    PropVal::Getter(a) | PropVal::Setter(a) | PropVal::Method(a) => {
                        Box::new(empty())
                    }
                    PropVal::Item(i) => Box::new(i.iter()),
                };
                let w: Box<dyn Iterator<Item = &I> + '_> = match &m.1 {
                    swc_tac::PropKey::Lit(_) => Box::new(empty()),
                    swc_tac::PropKey::Computed(c) => Box::new(once(c)),
                };
                v.chain(w)
            }))),
            Item::Select {
                cond,
                then,
                otherwise,
            } => Box::new([cond, then, otherwise].into_iter()),
            Item::StaticSubArray {
                begin,
                end,
                wrapped,
            } => Box::new(once(wrapped)),
            Item::StaticSubObject { wrapped, keys } => {
                Box::new(once(wrapped).chain(keys.iter().filter_map(|a| match a {
                    PropKey::Computed(a) => Some(a),
                    _ => None,
                })))
            } // Item::Intrinsic { value } => {
              //     let mut v = Vec::default();
              //     value
              //         .as_ref()
              //         .map(&mut |a| Ok::<_, Infallible>(v.push(a)))
              //         .unwrap();
              //     Box::new(v.into_iter())
              // }
        }
    }
    pub fn refs_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut I> + 'a> {
        use crate as swc_tac;
        match self {
            Item::Select {
                cond,
                then,
                otherwise,
            } => Box::new([cond, then, otherwise].into_iter()),
            swc_tac::Item::Just { id } => Box::new(once(id)),
            swc_tac::Item::Bin { left, right, op } => Box::new([left, right].into_iter()),
            swc_tac::Item::Un { arg, op } => Box::new(once(arg)),
            swc_tac::Item::Mem { obj, mem } => Box::new([obj, mem].into_iter()),
            Item::PrivateMem { obj, mem } | Item::HasPrivateMem { obj, mem } => Box::new(once(obj)),
            swc_tac::Item::Func { func, arrow } => Box::new(empty()),
            swc_tac::Item::Lit { lit } => Box::new(empty()),
            swc_tac::Item::Call { callee, args } => Box::new(
                match callee {
                    swc_tac::TCallee::Val(a) | TCallee::PrivateMember { func: a, member: _ } => {
                        vec![a]
                    }
                    swc_tac::TCallee::Member { func: r#fn, member } => vec![r#fn, member],
                    TCallee::Import | TCallee::Super | TCallee::Eval => vec![], // swc_tac::TCallee::Static(_) => vec![],
                }
                .into_iter()
                .chain(args.iter_mut().map(
                    |SpreadOr {
                         value: a,
                         is_spread: _,
                     }| a,
                )),
            ),
            Item::New { class, args } => Box::new(args.iter_mut().chain([class])),
            swc_tac::Item::Obj { members } => Box::new(members.iter_mut().flat_map(|m| {
                let v: Box<dyn Iterator<Item = &mut I> + '_> = match &mut m.1 {
                    PropVal::Getter(a) | PropVal::Setter(a) | PropVal::Method(a) => {
                        Box::new(empty())
                    }
                    PropVal::Item(i) => Box::new(once(i)),
                };
                let w: Box<dyn Iterator<Item = &mut I> + '_> = match &mut m.0 {
                    swc_tac::PropKey::Lit(_) => Box::new(empty()),
                    swc_tac::PropKey::Computed(c) => Box::new(once(c)),
                };
                v.chain(w)
            })),
            swc_tac::Item::Arr { members } => Box::new(members.iter_mut().map(
                |SpreadOr {
                     value: a,
                     is_spread: _,
                 }| a,
            )),
            swc_tac::Item::Yield { value, delegate } => Box::new(value.iter_mut()),
            swc_tac::Item::Await { value } => Box::new(once(value)),
            swc_tac::Item::Undef | Item::This | Item::Arguments | Item::Meta { .. } => {
                Box::new(empty())
            }
            Item::Asm { value } => Box::new(value.refs_mut()),
            Item::Class {
                superclass,
                members,
                constructor,
            } => Box::new(
                superclass
                    .iter_mut()
                    .chain(members.iter_mut().flat_map(|m| {
                        let v: Box<dyn Iterator<Item = &mut I> + '_> = match &mut m.2 {
                            PropVal::Getter(a) | PropVal::Setter(a) | PropVal::Method(a) => {
                                Box::new(empty())
                            }
                            PropVal::Item(i) => Box::new(i.iter_mut()),
                        };
                        let w: Box<dyn Iterator<Item = &mut I> + '_> = match &mut m.1 {
                            swc_tac::PropKey::Lit(_) => Box::new(empty()),
                            swc_tac::PropKey::Computed(c) => Box::new(once(c)),
                        };
                        v.chain(w)
                    })),
            ),
            Item::StaticSubArray {
                begin,
                end,
                wrapped,
            } => Box::new(once(wrapped)),
            Item::StaticSubObject { wrapped, keys } => {
                Box::new(once(wrapped).chain(keys.iter_mut().filter_map(|a| match a {
                    PropKey::Computed(a) => Some(a),
                    _ => None,
                })))
            } // Item::Intrinsic { value } => {
              //     let mut v = Vec::default();
              //     value
              //         .as_mut()
              //         .map(&mut |a| Ok::<_, Infallible>(v.push(a)))
              //         .unwrap();
              //     Box::new(v.into_iter())
              // }
        }
    }
}
