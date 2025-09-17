use crate::*;
impl cfg_traits::Func for TFunc {
    type Block = Id<TBlock>;

    type Blocks = Arena<TBlock>;

    fn blocks(&self) -> &Self::Blocks {
        &self.cfg.blocks
    }

    fn blocks_mut(&mut self) -> &mut Self::Blocks {
        &mut self.cfg.blocks
    }

    fn entry(&self) -> Self::Block {
        self.entry
    }
}
impl cfg_traits::Block<TFunc> for TBlock {
    type Terminator = TPostecedent;

    fn term(&self) -> &Self::Terminator {
        &self.post
    }

    fn term_mut(&mut self) -> &mut Self::Terminator {
        &mut self.post
    }
}
impl cfg_traits::Term<TFunc> for TPostecedent {
    type Target = Id<TBlock>;

    fn targets<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::Target> + 'a>
    where
        TFunc: 'a,
    {
        Box::new(
            match &self.catch {
                TCatch::Throw => None,
                TCatch::Jump { pat, k } => Some(k),
            }
            .into_iter()
            .chain(match &self.term {
                TTerm::Return(_) => {
                    Box::new(empty()) as Box<dyn Iterator<Item = &'a Self::Target> + 'a>
                }
                TTerm::Throw(_) => Box::new(empty()),
                TTerm::Jmp(id) => Box::new(once(id)),
                TTerm::CondJmp {
                    cond,
                    if_true,
                    if_false,
                } => Box::new([if_true, if_false].into_iter()),
                TTerm::Switch { x, blocks, default } => {
                    Box::new(blocks.iter().map(|a| &a.1).chain([default]))
                }
                TTerm::Default => Box::new(empty()),
            }),
        )
    }

    fn targets_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Self::Target> + 'a>
    where
        TFunc: 'a,
    {
        Box::new(
            match &mut self.catch {
                TCatch::Throw => None,
                TCatch::Jump { pat, k } => Some(k),
            }
            .into_iter()
            .chain(match &mut self.term {
                TTerm::Return(_) => {
                    Box::new(empty()) as Box<dyn Iterator<Item = &'a mut Self::Target> + 'a>
                }
                TTerm::Throw(_) => Box::new(empty()),
                TTerm::Jmp(id) => Box::new(once(id)),
                TTerm::CondJmp {
                    cond,
                    if_true,
                    if_false,
                } => Box::new([if_true, if_false].into_iter()),
                TTerm::Switch { x, blocks, default } => {
                    Box::new(blocks.iter_mut().map(|a| &mut a.1).chain([default]))
                }
                TTerm::Default => Box::new(empty()),
            }),
        )
    }
}
impl cfg_traits::Target<TFunc> for Id<TBlock> {
    fn block(&self) -> <TFunc as cfg_traits::Func>::Block {
        *self
    }

    fn block_mut(&mut self) -> &mut <TFunc as cfg_traits::Func>::Block {
        self
    }
}
impl cfg_traits::Term<TFunc> for Id<TBlock> {
    type Target = Id<TBlock>;

    fn targets<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::Target> + 'a>
    where
        TFunc: 'a,
    {
        Box::new(once(self))
    }

    fn targets_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Self::Target> + 'a>
    where
        TFunc: 'a,
    {
        Box::new(once(self))
    }
}
