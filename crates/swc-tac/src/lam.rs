use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    ops::{Index, IndexMut},
    sync::{Arc, OnceLock},
};

use arena_traits::{IndexAlloc, IndexIter};
use swc_atoms::Atom;
use swc_common::{Mark, SyntaxContext};
use swc_ecma_ast::Id;
pub trait AtomResolver: Debug {
    fn resolve(&self, len: usize) -> Atom;
}
impl<T: AtomResolver + ?Sized> AtomResolver for Arc<T> {
    fn resolve(&self, len: usize) -> Atom {
        (&**self).resolve(len)
    }
}
#[derive(Debug, Default)]
pub struct DefaultAtomResolver {}
impl AtomResolver for DefaultAtomResolver {
    fn resolve(&self, len: usize) -> Atom {
        Atom::new(format!("${len}"))
    }
}
#[derive(Debug)]
pub struct Prepend<V, A> {
    value: V,
    resolver: A,
}
impl<V: Display + Debug, A: AtomResolver> AtomResolver for Prepend<V, A> {
    fn resolve(&self, len: usize) -> Atom {
        let r = self.resolver.resolve(len);
        Atom::new(format!("{}{}", self.value, r))
    }
}
pub trait AtomResolverExt: AtomResolver {
    fn prepend<V>(self, value: V) -> Prepend<V, Self>
    where
        Self: Sized,
    {
        Prepend {
            value,
            resolver: self,
        }
    }
}
impl<T: AtomResolver + ?Sized> AtomResolverExt for T {}
#[derive(Clone, Debug)]
pub struct LAM<T> {
    map: HashMap<Id, T>,
    default: T,
    pub resolver: Arc<dyn AtomResolver>,
    ctxt: OnceLock<SyntaxContext>,
}
impl<T: Default> LAM<T> {
    pub fn new(resolver: impl AtomResolver + 'static) -> Self {
        Self {
            map: HashMap::new(),
            default: T::default(),
            resolver: Arc::new(resolver),
            ctxt: Default::default(),
        }
    }
}
impl<T: Default> Default for LAM<T> {
    fn default() -> Self {
        Self::new(DefaultAtomResolver {})
    }
}
impl<T> Index<Id> for LAM<T> {
    type Output = T;

    fn index(&self, index: Id) -> &Self::Output {
        match self.map.get(&index) {
            Some(value) => value,
            None => &self.default,
        }
    }
}
impl<T: Default> IndexMut<Id> for LAM<T> {
    fn index_mut(&mut self, index: Id) -> &mut Self::Output {
        self.map.entry(index).or_insert(T::default())
    }
}
impl<T: Default> IndexIter<Id> for LAM<T> {
    fn iter<'a>(&'a self) -> Box<(dyn Iterator<Item = Id> + 'a)> {
        Box::new(self.map.keys().cloned())
    }
}
impl<T: Default> IndexAlloc<Id> for LAM<T> {
    fn alloc(&mut self, value: Self::Output) -> Id {
        let len = self.map.len();
        let root = (
            self.resolver.resolve(len),
            *self
                .ctxt
                .get_or_init(|| SyntaxContext::empty().apply_mark(Mark::fresh(Mark::root()))),
        );
        self[root.clone()] = value;
        return root;
    }
}
