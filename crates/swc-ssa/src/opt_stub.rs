use portal_jsc_swc_util::SemanticCfg;

use crate::*;
pub struct OptStub {
    map: BTreeMap<Id<SBlock>, Id<SBlock>>,
}
impl OptStub {
    fn go(
        &mut self,
        i: &SCfg,
        o: &mut SCfg,
        sematic: &SemanticCfg,
        k: Id<SBlock>,
    ) -> anyhow::Result<Id<SBlock>> {
        loop {
            if let Some(k) = self.map.get(&k) {
                return Ok(*k);
            }
            let l = o.blocks.alloc(Default::default());
            self.map.insert(k, l);

            let baseline: BTreeMap<Id<SValueW>, Id<SValueW>> = i.blocks[k]
                .params
                .iter()
                .map(|a| (a.0, o.add_blockparam(l)))
                .collect();
            o.blocks[l].postcedent.catch = match &i.blocks[k].postcedent.catch {
                SCatch::Throw => SCatch::Throw,
                SCatch::Just { target } => SCatch::Just {
                    target: STarget {
                        block: self.go(i, o, sematic, target.block)?,
                        args: target
                            .args
                            .iter()
                            .filter_map(|a| baseline.get(a))
                            .cloned()
                            .collect(),
                    },
                },
            };
            let mut variants: BTreeMap<Id<SBlock>, BTreeMap<Id<SValueW>, Id<SValueW>>> =
                [(l, baseline)].into_iter().collect();
            for ins in i.blocks[k].stmts.iter().cloned() {
                for (a, mut b) in take(&mut variants) {
                    match &i.values[ins].value {
                        
                        v => {
                            let v = v.as_ref().map(
                                self,
                                &mut |_, i| b.get(i).cloned().context("in getting the value"),
                                &mut |s, b| s.go(i, o, sematic, *b),
                                &mut |_, f| todo!(),
                            )?;
                            let c = o.values.alloc(SValueW { value: v });
                            o.blocks[a].stmts.push(c);
                            b.insert(ins, c);
                            variants.insert(a, b);
                        }
                    }
                }
            }
            for (var, baseline) in variants.into_iter() {
                macro_rules! tgt {
                    ($e:expr) => {
                        match $e {
                            target => STarget {
                                block: self.go(i, o, sematic, target.block)?,
                                args: target
                                    .args
                                    .iter()
                                    .filter_map(|a| baseline.get(a))
                                    .cloned()
                                    .collect(),
                            },
                        }
                    };
                }
                o.blocks[var].postcedent.term = match &i.blocks[k].postcedent.term {
                    STerm::Throw(a) => {
                        STerm::Throw(baseline.get(a).cloned().context("in getting the value")?)
                    }
                    STerm::Return(r) => STerm::Return(match r {
                        None => None,
                        Some(a) => Some(baseline.get(a).cloned().context("in getting the value")?),
                    }),
                    STerm::Jmp(starget) => STerm::Jmp(tgt!(starget)),
                    STerm::CondJmp {
                        cond,
                        if_true,
                        if_false,
                    } => STerm::CondJmp {
                        cond: baseline
                            .get(cond)
                            .cloned()
                            .context("in getting the value")?,
                        if_true: tgt!(if_true),
                        if_false: tgt!(if_false),
                    },
                    STerm::Switch { x, blocks, default } => STerm::Switch {
                        x: baseline.get(x).cloned().context("in getting the value")?,
                        blocks: {
                            let mut blocks2: Vec<(Id<SValueW>, STarget)> = Vec::default();
                            for (a, b) in blocks.iter() {
                                blocks2.push((
                                    baseline.get(a).cloned().context("in getting the value")?,
                                    tgt!(b),
                                ));
                            }
                            blocks2
                        },
                        default: tgt!(default),
                    },
                    STerm::Default => STerm::Default,
                };
            }
        }
    }
}
