use crate::*;
impl ItemGetter<Ident,TFunc> for TCfg {
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
