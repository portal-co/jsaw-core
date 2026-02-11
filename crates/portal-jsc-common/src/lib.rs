//! Common types and utilities for the Portal JSC (JavaScript Compiler) project.
//!
//! This crate provides foundational types used across all stages of the JavaScript
//! compilation pipeline. It includes:
//!
//! - [`natives`]: Definitions for native/intrinsic functions and primordial objects
//! - [`semantic`]: Semantic analysis utilities and configurations
//! - [`syntax`]: Syntax-related helpers including import maps and inline assembly
//! - [`RefOrMut`]: A utility enum for handling references that may or may not be mutable
//!
//! This crate is `no_std` compatible for use in embedded or constrained environments.

#![no_std]
use core::{iter::once, mem::take, ops::Deref};
pub use portal_pc_asm_common as asm;
pub mod natives;
pub mod semantic;
pub mod syntax;

/// A reference that can be either immutable or mutable.
///
/// This enum allows code to generically handle both `&T` and `&mut T` references,
/// deferencing to the underlying value regardless of mutability. This is useful
/// in algorithms that need to traverse data structures where some paths require
/// mutation and others don't.
///
/// # Examples
///
/// ```ignore
/// use portal_jsc_common::RefOrMut;
///
/// fn process(data: RefOrMut<Vec<i32>>) {
///     // Can read from data regardless of whether it's Ref or Mut
///     println!("Length: {}", data.len());
/// }
/// ```
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum RefOrMut<'a, T: ?Sized> {
    /// An immutable reference to `T`
    Ref(&'a T),
    /// A mutable reference to `T`
    Mut(&'a mut T),
}
impl<'a, T: ?Sized> Deref for RefOrMut<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Ref(a) => a,
            Self::Mut(a) => a,
        }
    }
}
impl<'a, T> RefOrMut<'a, T> {
    /// Creates a new `RefOrMut` with a shorter lifetime from this one.
    ///
    /// This is useful when you need to create a temporary reference with a
    /// shorter lifetime, preserving the mutability of the original.
    pub fn bud<'b: 'a>(&'b mut self) -> RefOrMut<'b, T> {
        match self {
            Self::Ref(a) => Self::Ref(&**a),
            Self::Mut(a) => Self::Mut(&mut **a),
        }
    }

    /// Consumes the value, either by cloning (if immutable) or taking (if mutable).
    ///
    /// For immutable references, this clones the value. For mutable references,
    /// this takes the value and replaces it with the default.
    ///
    /// # Requirements
    ///
    /// The type `T` must implement both `Clone` and `Default`.
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
/// Macro for creating a derived `RefOrMut` by applying a transformation.
///
/// This macro takes a `RefOrMut` and a closure pattern, and produces a new
/// `RefOrMut` pointing to a sub-field or derived value, preserving mutability.
///
/// # Syntax
///
/// ```ignore
/// ref_or_mut_sub!(value => |pattern| expression)
/// ```
///
/// # Example
///
/// ```ignore
/// use portal_jsc_common::{RefOrMut, ref_or_mut_sub};
///
/// struct Container { field: i32 }
/// let mut container = Container { field: 42 };
/// let ref_or_mut = RefOrMut::Mut(&mut container);
/// let field_ref = ref_or_mut_sub!(ref_or_mut => |c| c.field);
/// ```
#[macro_export]
macro_rules! ref_or_mut_sub {
    ($a:expr => |$b:pat_param|$c:expr) => {
        match $a {
            $crate::RefOrMut::Ref($b) => $crate::RefOrMut::Ref(&$c),
            $crate::RefOrMut::Mut($b) => $crate::RefOrMut::Mut(&mut $c),
        }
    };
}
