//! Semantic analysis flags and configuration for JavaScript compilation.
//!
//! This module defines semantic modes and constraints that affect how JavaScript
//! code is compiled and optimized. Different flags enable or disable various
//! optimizations based on assumptions about the runtime environment.

bitflags::bitflags! {
    /// Semantic flags that control compilation behavior and optimizations.
    ///
    /// These flags represent assumptions or constraints about the JavaScript code
    /// and runtime environment. When a flag is set, the compiler can make stronger
    /// assumptions and perform more aggressive optimizations.
    #[repr(transparent)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
    pub struct SemanticFlags: u64{
        /// Assumes no monkey-patching of built-in objects and methods.
        ///
        /// When set, the compiler can assume that standard methods like
        /// `Array.prototype.push` or `Object.getOwnPropertyDescriptor` have
        /// not been modified from their original implementations.
        const NO_MONKEYPATCHING = 0x1;

        /// Disables JIT (Just-In-Time) compilation-specific optimizations.
        ///
        /// May be used for ahead-of-time compilation scenarios where JIT
        /// assumptions don't apply.
        const NO_JIT = 0x2;

        /// Asserts that any value equals itself (x === x is always true).
        ///
        /// In standard JavaScript, NaN is the only value where `x === x` is false.
        /// When this flag is set, the compiler can assume NaN is absent from the
        /// program, allowing it to use `x === x` checks and optimizations that
        /// would otherwise be incorrect in the presence of NaN.
        const BITWISE_OR_ABSENT_NAN = 0x4;

        /// Treats `~` plugin imports specially.
        ///
        /// Some build systems use `~` as a prefix for special import resolution.
        const PLUGIN_AS_TILDE_PLUGIN = 0x8;

        /// Disables support for "crazy" JavaScript features.
        ///
        /// This may exclude rarely-used or problematic JavaScript features
        /// to simplify compilation and improve performance.
        const NO_CRAZY = 0x10;

        /// Enables recognition and optimization of native functions.
        ///
        /// When set, the compiler recognizes and optimizes calls to
        /// native/intrinsic functions defined in the `natives` module.
        const NATIVES = 0x20;

        /// Assumes all objects are frozen (immutable).
        ///
        /// When set, the compiler can assume objects won't be modified,
        /// enabling more aggressive constant propagation and optimization.
        const ALL_OBJECTS_FROZEN = 0x40;

        /// Assumes function properties (like `name`, `length`) are sealed.
        ///
        /// When set, the compiler can assume standard function properties
        /// cannot be redefined or deleted.
        const FUNCTION_PROPERTIES_SEALED = 0x80;
    }
}
/// Semantic compilation target.
///
/// Specifies the target JavaScript engine or variant for compilation. Different
/// targets may have different semantics or capabilities, allowing the compiler
/// to generate optimized code for specific environments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
#[non_exhaustive]
pub enum SemanticTarget {
    /// Standard ECMAScript - the default target
    #[default]
    ECMAScript,
    /// Simpl - a simplified JavaScript variant
    Simpl(SimplVersion),
    /// MuJSC - a JavaScript engine variant
    MuJSC(MuJSCVersion),
    /// Porffor - another JavaScript engine variant
    Porffor(PorfforVersion),
}

/// Version information for MuJSC target.
///
/// MuJSC is a JavaScript engine implementation: <https://github.com/tsoding/mujsc/tree/main>
///
/// Currently has no versions defined (the enum is empty and `#[non_exhaustive]`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum MuJSCVersion {}

/// Version information for Porffor target.
///
/// Porffor is a JavaScript engine and compiler: <https://github.com/CanadaHonk/porffor>
///
/// Currently has no versions defined (the enum is empty and `#[non_exhaustive]`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum PorfforVersion {}

/// Version information for Simpl target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum SimplVersion {
    /// Legacy version of Simpl
    Legacy,
}
