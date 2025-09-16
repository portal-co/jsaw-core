#![no_std]
use core::{iter::once, mem::take, ops::Deref};
pub use portal_pc_asm_common as asm;

use either::Either;
bitflags::bitflags! {
    #[repr(transparent)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
    pub struct SemanticFlags: u64{
        const ASSUME_SES = 0x1;
        const ASSUME_AOT = 0x2;
        const BITWISE_OR_ABSENT_NAN = 0x4;
        const PLUGIN_AS_TILDE_PLUGIN = 0x8;
        const ASSUME_NORMAL = 0x10;
        const NATIVES = 0x20;
    }
}
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum RefOrMut<'a, T: ?Sized> {
    Ref(&'a T),
    Mut(&'a mut T),
}
impl<'a, T: ?Sized> Deref for RefOrMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Ref(a) => &**a,
            Self::Mut(a) => &**a,
        }
    }
}
impl<'a, T> RefOrMut<'a, T> {
    pub fn bud<'b: 'a>(&'b mut self) -> RefOrMut<'b, T> {
        match self {
            Self::Ref(a) => Self::Ref(&**a),
            Self::Mut(a) => Self::Mut(&mut **a),
        }
    }
    pub fn consume(&mut self) -> T
    where
        T: Clone + Default,
    {
        match self {
            RefOrMut::Ref(a) => Clone::clone(&**a),
            RefOrMut::Mut(a) => take(&mut **a),
        }
    }
}
#[macro_export]
macro_rules! ref_or_mut_sub {
    ($a:expr => |$b:pat_param|$c:expr) => {
        match $a {
            $crate::RefOrMut::Ref($b) => $crate::RefOrMut::Ref(&$c),
            $crate::RefOrMut::Mut($b) => $crate::RefOrMut::Mut(&mut $c),
        }
    };
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[non_exhaustive]
pub enum Native<E> {
    AssertString { value: E, comptime: bool },
    AssertNumber { value: E, comptime: bool },
    AssertStaticFn { value: E, comptime: bool },
    FastAdd { lhs: E, rhs: E },
    FastAnd { lhs: E, rhs: E },
    FastOr { lhs: E, rhs: E },
    FastEq { lhs: E, rhs: E },
    FastSub { lhs: E, rhs: E },
    FastMul { lhs: E, rhs: E, imul: bool },
    FastShl { lhs: E, rhs: E },
    InlineMe { n: Option<E> },
}
impl Native<()> {
    pub fn all() -> impl Iterator<Item = Self> {
        [
            "fast_add",
            "fast_and",
            "fast_or",
            "fast_eq",
            "fast_sub",
            "fast_shl",
            "fast_mul",
            "fast_imul",
            "inlineme",
            "inlineme_n",
        ]
        .into_iter()
        .filter_map(|a| Self::of(a))
        .chain([true, false].into_iter().flat_map(|a| {
            [
                Self::AssertNumber {
                    value: (),
                    comptime: a,
                },
                Self::AssertStaticFn {
                    value: (),
                    comptime: a,
                },
                Self::AssertString {
                    value: (),
                    comptime: a,
                },
            ]
        }))
    }
    pub fn of(a: &str) -> Option<Self> {
        Some(match a {
            "assert_string" => Self::AssertString {
                value: (),
                comptime: false,
            },
            "assert_number" => Self::AssertNumber {
                value: (),
                comptime: false,
            },
            "assert_static_fn" => Self::AssertStaticFn {
                value: (),
                comptime: false,
            },
            "comptime_string" => Self::AssertString {
                value: (),
                comptime: true,
            },
            "comptime_number" => Self::AssertNumber {
                value: (),
                comptime: true,
            },
            "comptime_static_fn" => Self::AssertStaticFn {
                value: (),
                comptime: true,
            },
            "fast_add" => Self::FastAdd { lhs: (), rhs: () },
            "fast_and" => Self::FastAnd { lhs: (), rhs: () },
            "fast_or" => Self::FastOr { lhs: (), rhs: () },
            "fast_eq" => Self::FastEq { lhs: (), rhs: () },
            "fast_sub" => Self::FastSub { lhs: (), rhs: () },
            "fast_shl" => Self::FastShl { lhs: (), rhs: () },
            "fast_mul" => Self::FastMul {
                lhs: (),
                rhs: (),
                imul: false,
            },
            "fast_imul" => Self::FastMul {
                lhs: (),
                rhs: (),
                imul: true,
            },
            "inlineme" => Self::InlineMe { n: None },
            "inlineme_n" => Self::InlineMe { n: Some(()) },
            _ => return None,
        })
    }
}
impl<E> Native<E> {
    pub fn key(&self) -> &'static str {
        match self {
            Native::AssertString { value, comptime } => {
                if *comptime {
                    "comptime_string"
                } else {
                    "assert_string"
                }
            }
            Native::AssertNumber { value, comptime } => {
                if *comptime {
                    "comptime_number"
                } else {
                    "aasert_number"
                }
            }
            Native::AssertStaticFn { value, comptime } => {
                if *comptime {
                    "comptime_static_fn"
                } else {
                    "assert_static_fn"
                }
            }
            Native::FastAdd { lhs, rhs } => "fast_add",
            Native::FastAnd { lhs, rhs } => "fast_and",
            Native::FastOr { lhs, rhs } => "fast_or",
            Native::FastEq { lhs, rhs } => "fast_eq",
            Native::FastSub { lhs, rhs } => "fast_sub",
            Native::FastMul { lhs, rhs, imul } => {
                if *imul {
                    "fast_imul"
                } else {
                    "fast_mul"
                }
            }
            Native::FastShl { lhs, rhs } => "fast_shl",
            Native::InlineMe { n } => match n {
                None => "inlineme",
                Some(_) => "inlineme_n",
            },
        }
    }
    pub fn as_ref<'a>(&'a self) -> Native<&'a E> {
        match self {
            Native::AssertString { value, comptime } => Native::AssertString {
                value,
                comptime: *comptime,
            },
            Native::AssertNumber { value, comptime } => Native::AssertNumber {
                value,
                comptime: *comptime,
            },
            Native::AssertStaticFn { value, comptime } => Native::AssertStaticFn {
                value,
                comptime: *comptime,
            },
            Native::FastAdd { lhs, rhs } => Native::FastAdd { lhs, rhs },
            Native::FastAnd { lhs, rhs } => Native::FastAnd { lhs, rhs },
            Native::FastOr { lhs, rhs } => Native::FastOr { lhs, rhs },
            Native::FastEq { lhs, rhs } => Native::FastEq { lhs, rhs },
            Native::FastSub { lhs, rhs } => Native::FastSub { lhs, rhs },
            Native::FastMul { lhs, rhs, imul } => Native::FastMul {
                lhs,
                rhs,
                imul: *imul,
            },
            Native::FastShl { lhs, rhs } => Native::FastShl { lhs, rhs },
            Native::InlineMe { n } => Native::InlineMe { n: n.as_ref() },
        }
    }
    pub fn as_mut<'a>(&'a mut self) -> Native<&'a mut E> {
        match self {
            Native::AssertString { value, comptime } => Native::AssertString {
                value,
                comptime: *comptime,
            },
            Native::AssertNumber { value, comptime } => Native::AssertNumber {
                value,
                comptime: *comptime,
            },
            Native::AssertStaticFn { value, comptime } => Native::AssertStaticFn {
                value,
                comptime: *comptime,
            },
            Native::FastAdd { lhs, rhs } => Native::FastAdd { lhs, rhs },
            Native::FastAnd { lhs, rhs } => Native::FastAnd { lhs, rhs },
            Native::FastOr { lhs, rhs } => Native::FastOr { lhs, rhs },
            Native::FastEq { lhs, rhs } => Native::FastEq { lhs, rhs },
            Native::FastSub { lhs, rhs } => Native::FastSub { lhs, rhs },
            Native::FastMul { lhs, rhs, imul } => Native::FastMul {
                lhs,
                rhs,
                imul: *imul,
            },
            Native::FastShl { lhs, rhs } => Native::FastShl { lhs, rhs },
            Native::InlineMe { n } => Native::InlineMe { n: n.as_mut() },
        }
    }
    pub fn map<E2, Er>(
        self,
        f: &mut (dyn FnMut(E) -> Result<E2, Er> + '_),
    ) -> Result<Native<E2>, Er> {
        Ok(match self {
            Native::AssertString { value, comptime } => Native::AssertString {
                value: f(value)?,
                comptime,
            },
            Native::AssertNumber { value, comptime } => Native::AssertNumber {
                value: f(value)?,
                comptime,
            },
            Native::AssertStaticFn { value, comptime } => Native::AssertStaticFn {
                value: f(value)?,
                comptime,
            },
            Native::FastAdd { lhs, rhs } => Native::FastAdd {
                lhs: f(lhs)?,
                rhs: f(rhs)?,
            },
            Native::FastAnd { lhs, rhs } => Native::FastAnd {
                lhs: f(lhs)?,
                rhs: f(rhs)?,
            },
            Native::FastOr { lhs, rhs } => Native::FastOr {
                lhs: f(lhs)?,
                rhs: f(rhs)?,
            },
            Native::FastEq { lhs, rhs } => Native::FastEq {
                lhs: f(lhs)?,
                rhs: f(rhs)?,
            },
            Native::FastSub { lhs, rhs } => Native::FastSub {
                lhs: f(lhs)?,
                rhs: f(rhs)?,
            },
            Native::FastMul { lhs, rhs, imul } => Native::FastMul {
                lhs: f(lhs)?,
                rhs: f(rhs)?,
                imul,
            },
            Native::FastShl { lhs, rhs } => Native::FastShl {
                lhs: f(lhs)?,
                rhs: f(rhs)?,
            },
            Native::InlineMe { n } => Native::InlineMe {
                n: match n {
                    None => None,
                    Some(n) => Some(f(n)?),
                },
            },
        })
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ImportMap<T> {
    Default,
    Star,
    Named { name: T },
}
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum Asm<I> {
    OrZero(I),
}
impl<I> Asm<I> {
    pub fn as_ref(&self) -> Asm<&I> {
        match self {
            Asm::OrZero(a) => Asm::OrZero(a),
        }
    }
    pub fn as_mut(&mut self) -> Asm<&mut I> {
        match self {
            Asm::OrZero(a) => Asm::OrZero(a),
        }
    }
    pub fn map<J, E>(self, f: &mut impl FnMut(I) -> Result<J, E>) -> Result<Asm<J>, E> {
        Ok(match self {
            Asm::OrZero(a) => Asm::OrZero(f(a)?),
        })
    }
    pub fn refs(&self) -> impl Iterator<Item = &I> {
        match self {
            Asm::OrZero(a) => once(a),
        }
    }
    pub fn refs_mut(&mut self) -> impl Iterator<Item = &mut I> {
        match self {
            Asm::OrZero(a) => once(a),
        }
    }
}
