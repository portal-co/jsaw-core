//! Block-level liveness over TAC variables, used to bound SSA threading.
//!
//! The TAC→SSA converter historically gave *every* block one block-param per
//! declared variable and threaded the entire `all` set through every jump and
//! every catch shim. For the generated stack-machine functions jsaw emits
//! (hundreds of blocks, each wrapped in a labelled-`break` catch shim), that
//! made both time and memory super-linear in `|decls| * |blocks|`.
//!
//! This module computes classic backward liveness over the TAC CFG so the
//! converter can thread only the variables actually live at each block entry.
//! The analysis is deliberately conservative: any variable whose liveness is
//! uncertain stays live, which is always safe (threading a dead variable is
//! harmless; *dropping* a live one would be a miscompile).

use std::collections::{BTreeMap, BTreeSet};

use swc_ecma_ast::Id as Ident;
use swc_tac::{LId, TCatch, TCfg, TTerm};

use swc_tac::TBlockId;

/// Per-block liveness over the variable universe `all`.
pub struct Liveness {
    /// Variables live at the entry of each block.
    pub live_in: BTreeMap<TBlockId, BTreeSet<Ident>>,
    /// Variables live at the exit of each block (before the terminator).
    pub live_out: BTreeMap<TBlockId, BTreeSet<Ident>>,
}

impl Liveness {
    /// Variables live at a block's entry, empty if the block was unreachable
    /// or unknown.
    pub fn at_entry(&self, block: TBlockId) -> &BTreeSet<Ident> {
        static EMPTY: BTreeSet<Ident> = BTreeSet::new();
        self.live_in.get(&block).unwrap_or(&EMPTY)
    }

    /// Variables live at a block's exit, empty if unreachable or unknown.
    pub fn at_exit(&self, block: TBlockId) -> &BTreeSet<Ident> {
        static EMPTY: BTreeSet<Ident> = BTreeSet::new();
        self.live_out.get(&block).unwrap_or(&EMPTY)
    }
}

/// Compute liveness over `cfg`, restricted to variables in `all`.
///
/// `all` is the converter's full threading set (declared variables plus
/// reassigned parameters). Variables outside it are never SSA-threaded and so
/// are excluded from the sets, keeping them small.
pub fn compute(cfg: &TCfg, all: &BTreeSet<Ident>) -> Liveness {
    // Successors: normal terminator edges plus the exceptional catch edge.
    let mut succs: BTreeMap<TBlockId, Vec<TBlockId>> = BTreeMap::new();
    let mut use_set: BTreeMap<TBlockId, BTreeSet<Ident>> = BTreeMap::new();
    let mut def_set: BTreeMap<TBlockId, BTreeSet<Ident>> = BTreeMap::new();

    for (bid, block) in cfg.blocks.iter() {
        let mut succ = Vec::new();
        match &block.post.term {
            TTerm::Jmp(t) => succ.push(*t),
            TTerm::CondJmp {
                if_true, if_false, ..
            } => {
                succ.push(*if_true);
                succ.push(*if_false);
            }
            TTerm::Switch { blocks, default, .. } => {
                succ.extend(blocks.iter().map(|(_, t)| *t));
                succ.push(*default);
            }
            TTerm::Return(_) | TTerm::Throw(_) | TTerm::Tail { .. } | TTerm::Default => {}
        }
        if let TCatch::Jump { k, .. } = &block.post.catch {
            succ.push(*k);
        }
        succs.insert(bid, succ);

        // Per-block use/def over the restricted universe. A variable is in
        // `use` if read before any assignment in the block, in `def` if
        // assigned anywhere in the block. Walking statements in order and
        // only adding to `use` when not yet locally defined gives the classic
        // upward-exposed-use set.
        let mut uses: BTreeSet<Ident> = BTreeSet::new();
        let mut defs: BTreeSet<Ident> = BTreeSet::new();
        let mut note_reads = |reads: &mut dyn Iterator<Item = &Ident>,
                              uses: &mut BTreeSet<Ident>,
                              defs: &BTreeSet<Ident>| {
            for r in reads {
                if all.contains(r) && !defs.contains(r) {
                    uses.insert((*r).clone());
                }
            }
        };
        for stmt in &block.stmts {
            // Right-hand side reads happen before the left-hand store.
            note_reads(&mut stmt.right.refs(), &mut uses, &defs);
            // The store target. Only plain identifier stores define; member
            // targets both read (the object) and store through it.
            match &stmt.left {
                LId::Id { id } => {
                    if all.contains(id) {
                        defs.insert(id.clone());
                    }
                }
                other => {
                    // Reads embedded in the assignment target (e.g. the object
                    // of a member store) are uses.
                    note_reads(&mut other.as_ref().refs(), &mut uses, &defs);
                }
            }
        }
        // Terminator reads.
        let term_reads: Vec<Ident> = match &block.post.term {
            TTerm::Return(r) => r.iter().cloned().collect(),
            TTerm::Throw(e) => vec![e.clone()],
            TTerm::CondJmp { cond, .. } => vec![cond.clone()],
            TTerm::Switch { x, blocks, .. } => {
                let mut v = vec![x.clone()];
                v.extend(blocks.iter().map(|(case, _)| case.clone()));
                v
            }
            TTerm::Tail { callee, args } => {
                let mut v: Vec<Ident> = args.iter().map(|a| a.value.clone()).collect();
                match callee {
                    swc_tac::TCallee::Val(c)
                    | swc_tac::TCallee::PrivateMember { func: c, .. } => v.push(c.clone()),
                    swc_tac::TCallee::Member { func, member } => {
                        v.push(func.clone());
                        v.push(member.clone());
                    }
                    _ => {}
                }
                v
            }
            TTerm::Jmp(_) | TTerm::Default => vec![],
        };
        note_reads(&mut term_reads.iter(), &mut uses, &defs);

        use_set.insert(bid, uses);
        def_set.insert(bid, defs);
    }

    // Backward fixed-point via a predecessor worklist:
    //   live_out[b] = ∪ live_in[s] for s in succ(b)
    //   live_in[b]  = use[b] ∪ (live_out[b] - def[b])
    // A block is only reprocessed when one of its successors' live_in grew,
    // which for reducible stack-machine CFGs converges in far fewer passes
    // than the naive whole-graph re-scan this replaces.
    let mut preds: BTreeMap<TBlockId, Vec<TBlockId>> = BTreeMap::new();
    for (b, ss) in &succs {
        for s in ss {
            preds.entry(*s).or_default().push(*b);
        }
    }

    let mut live_in: BTreeMap<TBlockId, BTreeSet<Ident>> = cfg
        .blocks
        .iter()
        .map(|(b, _)| (b, BTreeSet::new()))
        .collect();
    let mut live_out: BTreeMap<TBlockId, BTreeSet<Ident>> = live_in.clone();

    let mut worklist: std::collections::VecDeque<TBlockId> =
        cfg.blocks.iter().map(|(b, _)| b).collect();
    let mut in_worklist: BTreeSet<TBlockId> = worklist.iter().cloned().collect();

    while let Some(bid) = worklist.pop_front() {
        in_worklist.remove(&bid);
        let mut out: BTreeSet<Ident> = BTreeSet::new();
        if let Some(ss) = succs.get(&bid) {
            for s in ss {
                if let Some(si) = live_in.get(s) {
                    out.extend(si.iter().cloned());
                }
            }
        }
        let mut new_in = use_set.get(&bid).cloned().unwrap_or_default();
        if let Some(defs) = def_set.get(&bid) {
            for v in out.iter() {
                if !defs.contains(v) {
                    new_in.insert(v.clone());
                }
            }
        } else {
            new_in.extend(out.iter().cloned());
        }
        let in_changed = new_in != *live_in.get(&bid).unwrap_or(&BTreeSet::new());
        let out_changed = out != *live_out.get(&bid).unwrap_or(&BTreeSet::new());
        if in_changed {
            live_in.insert(bid, new_in);
        }
        if out_changed {
            live_out.insert(bid, out);
        }
        // If this block's live_in grew, its predecessors need reprocessing.
        if in_changed {
            if let Some(ps) = preds.get(&bid) {
                for p in ps {
                    if in_worklist.insert(*p) {
                        worklist.push_back(*p);
                    }
                }
            }
        }
    }

    Liveness { live_in, live_out }
}
