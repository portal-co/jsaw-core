#![no_std]
use core::{iter::once, mem::take, ops::Deref};
pub use portal_pc_asm_common as asm;

use either::Either;
pub mod semantic;
pub mod natives;
pub mod syntax;
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


