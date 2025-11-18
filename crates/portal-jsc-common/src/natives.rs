//! Native functions and primordial objects for JavaScript runtime.
//!
//! This module defines intrinsic functions and global objects that are built into
//! the JavaScript runtime. These are used during compilation to recognize and
//! optimize calls to well-known functions like `Math.imul` or `Reflect.get`.

use crate::*;

/// Primordial (built-in) JavaScript objects and functions.
///
/// These represent global objects and their methods that are part of the JavaScript
/// specification and can be specially handled by the compiler for optimization.
///
/// Note: Some variant names use snake_case (e.g., `Reflect_get`) to represent
/// the hierarchical relationship (object.method). These may be renamed in future
/// versions to use a more idiomatic representation.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum Primordial {
    /// The global `this` object (also available as `window`, `self`, or `global`)
    GlobalThis,
    /// The `Object` constructor
    Object,
    /// The `Reflect` namespace object
    Reflect,
    /// `Reflect.get` method
    // TODO: Consider renaming to ReflectGet for consistency
    Reflect_get,
    /// `Reflect.apply` method
    // TODO: Consider renaming to ReflectApply for consistency
    Reflect_apply,
    /// `Reflect.set` method
    // TODO: Consider renaming to ReflectSet for consistency
    Reflect_set,
    /// The `Math` namespace object
    Math,
    /// `Math.fround` method (note: currently misspelled as "froumd")
    // TODO: Consider renaming to MathFround for consistency and fixing typo
    Math_froumd,
    /// `Math.imul` method (32-bit integer multiplication)
    // TODO: Consider renaming to MathImul for consistency
    Math_imul,
}
impl Primordial {
    /// Looks up a primordial by its global name.
    ///
    /// Returns a static reference to the corresponding `Primordial` variant if the
    /// name matches a known global object, or `None` if not found.
    ///
    /// # Arguments
    ///
    /// * `k` - The global name to look up (e.g., "globalThis", "Object", "Math")
    pub fn global(k: &str) -> Option<&'static Self> {
        match k {
            "globalThis" | "window" | "self" | "global" => Some(&Self::GlobalThis),
            "Object" => Some(&Self::Object),
            "Reflect" => Some(&Self::Reflect),
            "Math" => Some(&Self::Math),
            _ => None,
        }
    }

    /// Looks up a method on this primordial object.
    ///
    /// For namespace objects like `Reflect` and `Math`, this resolves method names
    /// to their corresponding primordial variants. For `GlobalThis`, it recursively
    /// looks up global names.
    ///
    /// # Arguments
    ///
    /// * `k` - The method or property name to look up
    ///
    /// # Returns
    ///
    /// A static reference to the primordial representing the method, or `None` if
    /// the method is not a recognized primordial.
    pub fn get_perfect(&self, k: &str) -> Option<&'static Self> {
        match (self, k) {
            (Self::GlobalThis, a) => Self::global(a),
            (Self::Reflect, "get") => Some(&Self::Reflect_get),
            (Self::Reflect, "set") => Some(&Self::Reflect_set),
            (Self::Reflect, "apply") => Some(&Self::Reflect_apply),
            (Self::Math, "fround") => Some(&Self::Math_froumd),
            (Self::Math, "imul") => Some(&Self::Math_imul),
            _ => None,
        }
    }
}
/// Native (intrinsic) functions recognized by the compiler.
///
/// These represent special compiler-recognized functions that can be optimized
/// or have special semantics. They are typically exposed through a runtime library
/// and recognized by name during compilation.
///
/// The type parameter `E` represents the expression type used for arguments,
/// allowing this enum to be generic over different IR representations.
///
/// # Type Assertions
///
/// `AssertString`, `AssertNumber`, and `AssertStaticFn` variants are type assertions
/// that can be either runtime checks or compile-time only (when `comptime` is true).
///
/// # Fast Operations
///
/// `Fast*` variants represent optimized versions of JavaScript operations that
/// assume certain type constraints, allowing for more efficient code generation.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[non_exhaustive]
pub enum Native<E> {
    /// Assert that a value is a string (runtime or compile-time)
    AssertString { value: E, comptime: bool },
    /// Assert that a value is a number (runtime or compile-time)
    AssertNumber { value: E, comptime: bool },
    /// Assert that a value is a static function (runtime or compile-time)
    AssertStaticFn { value: E, comptime: bool },
    /// Fast addition operation (assumes numeric operands)
    FastAdd { lhs: E, rhs: E },
    /// Fast logical AND operation
    FastAnd { lhs: E, rhs: E },
    /// Fast logical OR operation
    FastOr { lhs: E, rhs: E },
    /// Fast equality comparison
    FastEq { lhs: E, rhs: E },
    /// Fast subtraction operation (assumes numeric operands)
    FastSub { lhs: E, rhs: E },
    /// Fast multiplication operation
    /// When `imul` is true, uses 32-bit integer multiplication semantics
    FastMul { lhs: E, rhs: E, imul: bool },
    /// Fast left shift operation (assumes integer operands)
    FastShl { lhs: E, rhs: E },
    /// Marker for functions that should be inlined
    /// 
    /// `n` controls inlining depth:
    /// - If `n` is specified and non-zero: inline the function and replace references to `n` with `n - 1`
    /// - If `n` is specified and zero, or not specified: remove the marker while inlining
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
