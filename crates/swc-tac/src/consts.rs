//! Constant evaluation and item resolution for TAC.
//!
//! This module implements the `ItemGetter` trait for `TCfg`, allowing
//! the TAC control flow graph to participate in constant evaluation
//! and item resolution.
//!
//! This enables optimization passes to:
//! - Look up definitions of identifiers
//! - Perform constant propagation
//! - Evaluate primordial functions
//! - Resolve native function calls

use crate::*;

impl<Ctx> ItemGetter<Ident, TFunc, Ctx> for TCfg {
    fn get_item<'a>(
        &'a self,
        i: (Atom, SyntaxContext),
        _ctx: Ctx,
    ) -> Option<&'a Item<(Atom, SyntaxContext), TFunc>>
    where
        Ctx: 'a,
    {
        self.def(LId::Id { id: i })
    }
    fn get_mut_item<'a>(
        &'a mut self,
        i: (Atom, SyntaxContext),
        _ctx: Ctx,
    ) -> Option<&'a mut Item<(Atom, SyntaxContext), TFunc>>
    where
        Ctx: 'a,
    {
        self.def_mut(LId::Id { id: i })
    }
    fn get_ident<'a>(&'a self, i: (Atom, SyntaxContext), _ctx: Ctx) -> Option<Ident>
    where
        Ctx: 'a,
    {
        Some(i)
    }
}
