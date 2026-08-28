//! Native functions and primordial objects for JavaScript runtime.
//!
//! This module defines intrinsic functions and global objects that are built into
//! the JavaScript runtime. These are used during compilation to recognize and
//! optimize calls to well-known functions like `Math.imul` or `Reflect.get`.

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
    /// `Reflect.has` method
    Reflect_has,
    /// `Reflect.ownKeys` method
    Reflect_ownKeys,
    /// `Reflect.construct` method
    Reflect_construct,
    /// `Reflect.deleteProperty` method
    Reflect_deleteProperty,
    /// `Reflect.defineProperty` method
    Reflect_defineProperty,
    /// `Reflect.getOwnPropertyDescriptor` method
    Reflect_getOwnPropertyDescriptor,
    /// `Reflect.getPrototypeOf` method
    Reflect_getPrototypeOf,
    /// `Reflect.setPrototypeOf` method
    Reflect_setPrototypeOf,
    /// `Reflect.isExtensible` method
    Reflect_isExtensible,
    /// `Reflect.preventExtensions` method
    Reflect_preventExtensions,
    /// The `Math` namespace object
    Math,
    /// `Math.fround` method (note: currently misspelled as "froumd")
    // TODO: Consider renaming to MathFround for consistency and fixing typo
    Math_fround,
    /// `Math.imul` method (32-bit integer multiplication)
    // TODO: Consider renaming to MathImul for consistency
    Math_imul,
    /// `Math.PI` constant
    Math_PI,
    /// `Math.E` constant
    Math_E,
    /// `Math.LN2` constant
    Math_LN2,
    /// `Math.LN10` constant
    Math_LN10,
    /// `Math.LOG2E` constant
    Math_LOG2E,
    /// `Math.LOG10E` constant
    Math_LOG10E,
    /// `Math.SQRT2` constant
    Math_SQRT2,
    /// `Math.SQRT1_2` constant
    Math_SQRT1_2,
    /// `Math.abs` method
    Math_abs,
    /// `Math.floor` method
    Math_floor,
    /// `Math.ceil` method
    Math_ceil,
    /// `Math.round` method
    Math_round,
    /// `Math.trunc` method
    Math_trunc,
    /// `Math.sign` method
    Math_sign,
    /// `Math.sqrt` method
    Math_sqrt,
    /// `Math.cbrt` method
    Math_cbrt,
    /// `Math.pow` method
    Math_pow,
    /// `Math.min` method
    Math_min,
    /// `Math.max` method
    Math_max,
    /// `Math.log` method
    Math_log,
    /// `Math.log2` method
    Math_log2,
    /// `Math.log10` method
    Math_log10,
    /// `Math.exp` method
    Math_exp,
    /// `Math.hypot` method
    Math_hypot,
    /// The `Array` constructor
    Array,
    /// `Array.isArray` method
    Array_isArray,
    /// `Object.keys` method
    Object_keys,
    /// `Object.values` method
    Object_values,
    /// `Object.entries` method
    Object_entries,
    /// `Object.assign` method
    Object_assign,
    /// `Object.create` method
    Object_create,
    /// `Object.freeze` method
    Object_freeze,
    /// `Object.isFrozen` method
    Object_isFrozen,
    /// `Object.getPrototypeOf` method
    Object_getPrototypeOf,
    /// `Object.setPrototypeOf` method
    Object_setPrototypeOf,
    /// `Object.defineProperty` method
    Object_defineProperty,
    /// `Object.defineProperties` method
    Object_defineProperties,
    /// `Object.getOwnPropertyDescriptor` method
    Object_getOwnPropertyDescriptor,
    /// `Object.getOwnPropertyDescriptors` method
    Object_getOwnPropertyDescriptors,
    /// `Object.getOwnPropertyNames` method
    Object_getOwnPropertyNames,
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
            "Array" => Some(&Self::Array),
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
            (Self::Reflect, "has") => Some(&Self::Reflect_has),
            (Self::Reflect, "ownKeys") => Some(&Self::Reflect_ownKeys),
            (Self::Reflect, "construct") => Some(&Self::Reflect_construct),
            (Self::Reflect, "deleteProperty") => Some(&Self::Reflect_deleteProperty),
            (Self::Reflect, "defineProperty") => Some(&Self::Reflect_defineProperty),
            (Self::Reflect, "getOwnPropertyDescriptor") => {
                Some(&Self::Reflect_getOwnPropertyDescriptor)
            }
            (Self::Reflect, "getPrototypeOf") => Some(&Self::Reflect_getPrototypeOf),
            (Self::Reflect, "setPrototypeOf") => Some(&Self::Reflect_setPrototypeOf),
            (Self::Reflect, "isExtensible") => Some(&Self::Reflect_isExtensible),
            (Self::Reflect, "preventExtensions") => Some(&Self::Reflect_preventExtensions),
            (Self::Math, "fround") => Some(&Self::Math_fround),
            (Self::Math, "imul") => Some(&Self::Math_imul),
            (Self::Math, "PI") => Some(&Self::Math_PI),
            (Self::Math, "E") => Some(&Self::Math_E),
            (Self::Math, "LN2") => Some(&Self::Math_LN2),
            (Self::Math, "LN10") => Some(&Self::Math_LN10),
            (Self::Math, "LOG2E") => Some(&Self::Math_LOG2E),
            (Self::Math, "LOG10E") => Some(&Self::Math_LOG10E),
            (Self::Math, "SQRT2") => Some(&Self::Math_SQRT2),
            (Self::Math, "SQRT1_2") => Some(&Self::Math_SQRT1_2),
            (Self::Math, "abs") => Some(&Self::Math_abs),
            (Self::Math, "floor") => Some(&Self::Math_floor),
            (Self::Math, "ceil") => Some(&Self::Math_ceil),
            (Self::Math, "round") => Some(&Self::Math_round),
            (Self::Math, "trunc") => Some(&Self::Math_trunc),
            (Self::Math, "sign") => Some(&Self::Math_sign),
            (Self::Math, "sqrt") => Some(&Self::Math_sqrt),
            (Self::Math, "cbrt") => Some(&Self::Math_cbrt),
            (Self::Math, "pow") => Some(&Self::Math_pow),
            (Self::Math, "min") => Some(&Self::Math_min),
            (Self::Math, "max") => Some(&Self::Math_max),
            (Self::Math, "log") => Some(&Self::Math_log),
            (Self::Math, "log2") => Some(&Self::Math_log2),
            (Self::Math, "log10") => Some(&Self::Math_log10),
            (Self::Math, "exp") => Some(&Self::Math_exp),
            (Self::Math, "hypot") => Some(&Self::Math_hypot),
            (Self::Array, "isArray") => Some(&Self::Array_isArray),
            (Self::Object, "keys") => Some(&Self::Object_keys),
            (Self::Object, "values") => Some(&Self::Object_values),
            (Self::Object, "entries") => Some(&Self::Object_entries),
            (Self::Object, "assign") => Some(&Self::Object_assign),
            (Self::Object, "create") => Some(&Self::Object_create),
            (Self::Object, "freeze") => Some(&Self::Object_freeze),
            (Self::Object, "isFrozen") => Some(&Self::Object_isFrozen),
            (Self::Object, "getPrototypeOf") => Some(&Self::Object_getPrototypeOf),
            (Self::Object, "setPrototypeOf") => Some(&Self::Object_setPrototypeOf),
            (Self::Object, "defineProperty") => Some(&Self::Object_defineProperty),
            (Self::Object, "defineProperties") => Some(&Self::Object_defineProperties),
            (Self::Object, "getOwnPropertyDescriptor") => {
                Some(&Self::Object_getOwnPropertyDescriptor)
            }
            (Self::Object, "getOwnPropertyDescriptors") => {
                Some(&Self::Object_getOwnPropertyDescriptors)
            }
            (Self::Object, "getOwnPropertyNames") => Some(&Self::Object_getOwnPropertyNames),
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
    /// Never executed; compilers can optimize this out
    Trim,
    /// Hint to the compiler that `value` is truthy at the current program point.
    ///
    /// Emitted by `DreamcompModuleCore::clean` on the surviving branch of a
    /// `CondJmp` whose other target was burnt (contained `trim()` or an
    /// uncompilable identifier).  The value is the branch condition — possibly
    /// negated when the *true* branch was the burnt one.
    ///
    /// Semantics: the wrapped value is evaluated (for side-effects) and the
    /// compiler is informed the result is truthy.  No runtime assertion is
    /// emitted; backends must lower this to a no-cost hint (e.g.
    /// `__builtin_assume` in C/LLVM).
    Assume { value: E },
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
            "trim",
            "assume",
        ]
        .into_iter()
        .filter_map(Self::of)
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
            "trim" => Self::Trim,
            "assume" => Self::Assume { value: () },
            _ => return None,
        })
    }
}
impl<E> Native<E> {
    pub fn key(&self) -> &'static str {
        match self {
            Native::Trim => "trim",
            Native::AssertString { value: _, comptime } => {
                if *comptime {
                    "comptime_string"
                } else {
                    "assert_string"
                }
            }
            Native::AssertNumber { value: _, comptime } => {
                if *comptime {
                    "comptime_number"
                } else {
                    "aasert_number"
                }
            }
            Native::AssertStaticFn { value: _, comptime } => {
                if *comptime {
                    "comptime_static_fn"
                } else {
                    "assert_static_fn"
                }
            }
            Native::FastAdd { lhs: _, rhs: _ } => "fast_add",
            Native::FastAnd { lhs: _, rhs: _ } => "fast_and",
            Native::FastOr { lhs: _, rhs: _ } => "fast_or",
            Native::FastEq { lhs: _, rhs: _ } => "fast_eq",
            Native::FastSub { lhs: _, rhs: _ } => "fast_sub",
            Native::FastMul {
                lhs: _,
                rhs: _,
                imul,
            } => {
                if *imul {
                    "fast_imul"
                } else {
                    "fast_mul"
                }
            }
            Native::FastShl { lhs: _, rhs: _ } => "fast_shl",
            Native::InlineMe { n } => match n {
                None => "inlineme",
                Some(_) => "inlineme_n",
            },
            Native::Assume { value: _ } => "assume",
        }
    }
    pub fn as_ref(&self) -> Native<&E> {
        match self {
            Native::Trim => Native::Trim,
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
            Native::Assume { value } => Native::Assume { value },
        }
    }
    pub fn as_mut(&mut self) -> Native<&mut E> {
        match self {
            Native::Trim => Native::Trim,
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
            Native::Assume { value } => Native::Assume { value },
        }
    }
    pub fn map<E2, Er>(
        self,
        f: &mut (dyn FnMut(E) -> Result<E2, Er> + '_),
    ) -> Result<Native<E2>, Er> {
        Ok(match self {
            Native::Trim => Native::Trim,
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
            Native::Assume { value } => Native::Assume { value: f(value)? },
        })
    }
}
