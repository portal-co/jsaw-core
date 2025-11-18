//! Syntax-related utilities for JavaScript compilation.
//!
//! This module provides types for representing import mapping and inline
//! assembly constructs during compilation.

use crate::*;

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ThisArg<T> {
    This,
    Val(T),
    NoThisArg,
}

/// Represents how a symbol is imported from a module.
///
/// JavaScript has three main import forms, each represented by a variant:
/// - Default imports: `import foo from 'module'`
/// - Namespace imports: `import * as foo from 'module'`
/// - Named imports: `import { foo } from 'module'`
///
/// The type parameter `T` represents the name type (typically a string or identifier).
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ImportMap<T> {
    /// Default import from a module
    Default,
    /// Namespace (star) import from a module
    Star,
    /// Named import with a specific name
    Named { name: T },
}

/// Inline assembly constructs for low-level operations.
///
/// These represent operations that may be expressed as inline assembly or
/// compiler intrinsics for performance-critical code paths.
///
/// The type parameter `I` represents the identifier or value type used in
/// the assembly operation.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[non_exhaustive]
pub enum Asm<I> {
    /// Bitwise OR with zero - a common idiom to convert values to integers
    /// Equivalent to `(x | 0)` in JavaScript
    OrZero(I),
}
impl<I> Asm<I> {
    /// Creates a reference to this assembly operation.
    pub fn as_ref(&self) -> Asm<&I> {
        match self {
            Asm::OrZero(a) => Asm::OrZero(a),
        }
    }

    /// Creates a mutable reference to this assembly operation.
    pub fn as_mut(&mut self) -> Asm<&mut I> {
        match self {
            Asm::OrZero(a) => Asm::OrZero(a),
        }
    }

    /// Maps the identifier/value in this assembly operation using the provided function.
    ///
    /// # Errors
    ///
    /// Returns an error if the mapping function fails.
    pub fn map<J, E>(self, f: &mut impl FnMut(I) -> Result<J, E>) -> Result<Asm<J>, E> {
        Ok(match self {
            Asm::OrZero(a) => Asm::OrZero(f(a)?),
        })
    }

    /// Returns an iterator over references to identifiers/values used in this operation.
    pub fn refs(&self) -> impl Iterator<Item = &I> {
        match self {
            Asm::OrZero(a) => once(a),
        }
    }

    /// Returns an iterator over mutable references to identifiers/values used in this operation.
    pub fn refs_mut(&mut self) -> impl Iterator<Item = &mut I> {
        match self {
            Asm::OrZero(a) => once(a),
        }
    }
}
