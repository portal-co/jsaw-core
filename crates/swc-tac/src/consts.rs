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
    fn native_of(&self, mut i: I) -> Option<Native<I>>
    where
        I: Clone,
    {
        loop {
            let g = self.get_item(i)?;
            let (mut func, mut member, args) = match g {
                Item::Just { id } => {
                    i = id.clone();
                    continue;
                }
                Item::Call {
                    callee: TCallee::Member { func, member },
                    args,
                } => (func, member, args),
                _ => return None,
            };
            loop {
                if let Some(i) = self.get_ident(func.clone()) {
                    if i.0 == "globalThis" {
                        break;
                    }
                }
                let Item::Just { id } = self.get_item(func.clone())? else {
                    return None;
                };
                func = id;
            }
            let n = loop {
                let id = match self.get_item(member.clone())? {
                    Item::Lit { lit: Lit::Str(s) } => {
                        if let Some(m) = s.value.strip_prefix("~Natives_") {
                            if let Some(m) = Native::of(m) {
                                break m;
                            }
                        }
                        return None;
                    }
                    Item::Just { id } => id,
                    _ => return None,
                };
                member = id;
            };
            let mut args = args.iter().cloned();
            return n
                .map::<I, ()>(&mut |_| match args.next() {
                    Some(SpreadOr(a,b)) if !b => Ok(a),
                    _ => Err(()),
                })
                .ok();
        }
    }
    fn inlinable(&self, d: &Item<I, F>) -> bool
    where
        I: Clone,
    {
        let tcfg = self;
        match d {
            Item::Just { id } => tcfg.get_item(id.clone()).is_some(),
            Item::Asm { value }
                if match value {
                    Asm::OrZero(value) => tcfg.get_item(value.clone()).is_some(),
                    _ => todo!(),
                } =>
            {
                true
            }
            Item::Lit { lit } => true,
            Item::Un { arg, op }
                if !matches!(op, UnaryOp::Delete) && tcfg.get_item(arg.clone()).is_some() =>
            {
                true
            }
            _ => false,
        }
    }
    fn simplify_just(&mut self, i: I) -> bool
    where
        Item<I, F>: Clone,
        I: Clone,
    {
        if let Some(g) = self.get_item(i.clone()).and_then(|j| match j {
            Item::Just { id } => self.get_item(id.clone()),
            _ => None,
        }) {
            if self.inlinable(g) {
                let g = g.clone();
                if let Some(h) = self.get_mut_item(i) {
                    *h = g;
                    return true;
                }
            }
        }
        return false;
    }
}
impl<T: ItemGetter<I, F> + ?Sized, I, F> ItemGetterExt<I, F> for T {}
