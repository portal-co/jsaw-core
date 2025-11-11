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

impl ItemGetter<Ident, TFunc> for TCfg {
    fn get_item(&self, i: (Atom, SyntaxContext)) -> Option<&Item<(Atom, SyntaxContext), TFunc>> {
        self.def(LId::Id { id: i })
    }
    fn get_mut_item(
        &mut self,
        i: (Atom, SyntaxContext),
    ) -> Option<&mut Item<(Atom, SyntaxContext), TFunc>> {
        self.def_mut(LId::Id { id: i })
    }
    fn get_ident(&self, i: (Atom, SyntaxContext)) -> Option<Ident> {
        Some(i)
    }
}
