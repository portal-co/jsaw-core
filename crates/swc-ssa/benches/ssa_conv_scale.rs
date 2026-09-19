//! Scale benchmark for `TFunc -> SFunc` conversion.
//!
//! Generates synthetic functions shaped like jsaw's blitz-js stack-machine
//! output: many sequential blocks, each declaring a fresh `let` temporary, so
//! `decls` grows with block count. The original converter was super-linear in
//! `|decls| * |blocks| * |stmts|`; this harness makes that visible.
//!
//! Run with:  cargo test --release --bench ssa_conv_scale -- --nocapture

use std::time::{Duration, Instant};

use swc_ecma_visit::VisitWith;
use swc_tac::TFunc;

use portal_jsc_swc_ssa::SFunc;

fn stack_machine_source(blocks: usize) -> String {
    // Each chunk declares a fresh `let tN`, so `decls` grows with `blocks` —
    // the exact super-linear shape the M19 artifact exposes.
    let mut src = String::from("export function f(sp) {\n  let acc = 0;\n");
    for n in 0..blocks {
        src.push_str(&format!(
            "  {{ let t{n} = sp + {n}; acc = (acc + t{n}) | 0; }}\n"
        ));
    }
    src.push_str("  return acc;\n}\n");
    src
}

fn convert_source(src: &str) -> Duration {
    portal_solutions_swibb::test::with_test_globals(|| {
        let cm = portal_solutions_swibb::test::swc_common::sync::Lrc::new(
            portal_solutions_swibb::test::swc_common::SourceMap::default(),
        );
        let module = portal_solutions_swibb::test::test_load(&cm, "bench", src);
        convert_module(module)
    })
}

fn convert_module(module: swc_ecma_ast::Module) -> Duration {
    struct V(Duration);
    impl swc_ecma_visit::Visit for V {
        fn visit_function(&mut self, node: &swc_ecma_ast::Function) {
            let tfunc = TFunc::try_from(node.clone()).unwrap();
            let start = Instant::now();
            let sfunc = SFunc::try_from(tfunc).unwrap();
            self.0 += start.elapsed();
            std::hint::black_box(sfunc.cfg.blocks.len());
        }
    }
    let mut v = V(Duration::ZERO);
    module.visit_with(&mut v);
    v.0
}

/// A labelled-loop shape matching blitz-js's real output: an outer `l0:`
/// loop containing many `lN:` inner chunks that `break lN` to a join, with a
/// mutated accumulator carried around the back edge. This is the shape that
/// blows up per-block threading (many preds/succs + a loop).
fn labeled_loop_source(blocks: usize) -> String {
    let mut src = String::from("export function f(sp) {\n  let acc = 0;\n  l0: while (sp > 0) {\n    sp = sp - 1;\n");
    for n in 0..blocks {
        src.push_str(&format!(
            "    l{n}: {{ let t{n} = sp + {n}; acc = (acc + t{n}) | 0; if (acc > 1000000) break l0; }}\n"
        ));
    }
    src.push_str("  }\n  return acc;\n}\n");
    src
}

/// Minimal repro for "jump argument count did not match its target": a
/// variable defined on one path of a join and read after it, under the
/// liveness-bounded threading. Run the full swc-ssa test suite for coverage;
/// this bench only needs to not panic on realistic shapes.
#[test]
fn ssa_conv_join_shapes() {
    let cases = [
        // join with a var defined only on one arm, used after
        "export function f(a){ let x; if(a){ x = 1; } else { x = 2; } return x; }",
        // loop-carried accumulator
        "export function f(n){ let s=0; for(let i=0;i<n;i++){ s+=i; } return s; }",
        // labelled break out of nested blocks
        "export function f(a){ let r=0; l0:{ let x=a; l1:{ if(x) { r=1; break l0; } r=2; break l1; } r=3; } return r; }",
        // try/catch with a catch var and carried state
        "export function f(a){ let s=0; try { s = a+1; } catch(e){ s = e; } return s; }",
        // reassigned param carried through a loop
        "export function f(n){ while(n>0){ n = n-1; } return n; }",
        // try/catch where a local is reassigned in try and read after
        "export function f(a){ let x=0; try { x = a; } catch(e){ x = 1; } return x; }",
        // try inside a loop with a carried var (jsaw stack-machine shape)
        "export function f(n){ let s=0; for(let i=0;i<n;i++){ try { s = s+i; } catch(e){ s=0; } } return s; }",
        // nested try/catch with break
        "export function f(a){ let r=0; l0: for(;;){ try { if(a){ r=1; break l0; } } catch(e){ r=2; } break l0; } return r; }",
        // revision-style: param used at return
        "export function run(x) { return x + 1; }",
        // var defined before try, reassigned in catch, read after
        "export function f(a){ let x=a; try { x = x+1; } catch(e){ x = 0; } return x; }",
    ];
    for (idx, src) in cases.iter().enumerate() {
        let result = std::panic::catch_unwind(|| convert_source(src));
        match result {
            Ok(t) => eprintln!("join_shape[{idx}] ok in {t:?}"),
            Err(_) => eprintln!("join_shape[{idx}] PANICKED: {src}"),
        }
    }
}

#[test]
fn ssa_conv_scale() {
    eprintln!("== straight-line ==");
    for blocks in [64usize, 128, 256, 512, 1024, 2048] {
        let src = stack_machine_source(blocks);
        let t = convert_source(&src);
        eprintln!("blocks={blocks:4}  TFunc->SFunc = {t:?}");
    }
    eprintln!("== labeled loop ==");
    for blocks in [64usize, 128, 256, 512, 1024] {
        let src = labeled_loop_source(blocks);
        let t = convert_source(&src);
        eprintln!("blocks={blocks:4}  TFunc->SFunc = {t:?}");
    }
}

#[test]
fn dbg_uninit_if_else() {
    let src = "export function f(cond) { let a; if (cond) { a = 10; } else { a = 20; } return a; }";
    portal_solutions_swibb::test::with_test_globals(|| {
        let cm = portal_solutions_swibb::test::swc_common::sync::Lrc::new(
            portal_solutions_swibb::test::swc_common::SourceMap::default(),
        );
        let module = portal_solutions_swibb::test::test_load(&cm, "dbg", src);
        use swc_ecma_visit::VisitWith;
        struct V;
        impl swc_ecma_visit::Visit for V {
            fn visit_function(&mut self, node: &swc_ecma_ast::Function) {
                let tfunc = TFunc::try_from(node.clone()).unwrap();
                let all: std::collections::BTreeSet<_> = tfunc.cfg.decls.clone();
                let liv = portal_jsc_swc_ssa::live::compute(&tfunc.cfg, &all);
                for (bid,blk) in tfunc.cfg.blocks.iter() {
                    eprintln!("  blk {:?} term={:?} catch={:?}", bid, blk.post.term, blk.post.catch);
                }
                for (b, s) in &liv.live_in {
                    eprintln!("live_in[{:?}] = {:?}", b, s.iter().map(|i| i.0.to_string()).collect::<Vec<_>>());
                }
                for (b, s) in &liv.live_out {
                    eprintln!("live_out[{:?}] = {:?}", b, s.iter().map(|i| i.0.to_string()).collect::<Vec<_>>());
                }
                let sfunc = SFunc::try_from(tfunc).unwrap();
                for (id, val) in sfunc.cfg.values.iter() {
                    match &val.value {
                        portal_jsc_swc_ssa::SValue::LoadId(i) => eprintln!("LOADID {:?}", i.0),
                        portal_jsc_swc_ssa::SValue::StoreId{target:i,..} => eprintln!("STOREID {:?}", i.0),
                        _=>{}
                    }
                }
            }
        }
        module.visit_with(&mut V);
    });
}
