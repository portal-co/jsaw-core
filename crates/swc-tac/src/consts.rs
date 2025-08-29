use crate::*;
pub trait ItemGetter<I = Ident, F = TFunc> {
    fn get_item(&self, i: I) -> Option<&Item<I, F>>;
    fn get_mut_item(&mut self, i: I) -> Option<&mut Item<I, F>>;
    fn get_ident(&self, i: I) -> Option<Ident>;
}
impl ItemGetter for TCfg {
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
pub trait ItemGetterExt<I, F>: ItemGetter<I, F> {
    fn simplify_just(&mut self, i: I) -> bool
    where
        Item<I, F>: Clone,
        I: Clone,
    {
        if let Some(g) = self.get_item(i.clone()).and_then(|j| match j {
            Item::Just { id } => self.get_item(id.clone()),
            _ => None,
        }) {
            let g = g.clone();
            if let Some(h) = self.get_mut_item(i) {
                *h = g;
                return true;
            }
        }
        return false;
    }
}
impl<T: ItemGetter<I, F>, I, F> ItemGetterExt<I, F> for T {}
