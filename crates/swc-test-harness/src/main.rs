//! Test harness binary: JS → CFG → TAC → CFG → JS roundtrip.
//!
//! Reads a JavaScript script file, pipes it through the jsaw-core IR pipeline
//! (parse → CfgModule → TModule → back to CFG → back to SWC AST), and writes
//! the reconstructed JavaScript to stdout.
//!
//! Used by the integration tests in `tests/roundtrip.rs` to verify that the
//! pipeline preserves program semantics.

use std::path::Path;

use anyhow::{Context, Result};
use swc_cfg::module::CfgModule;
use swc_common::{SourceMap, GLOBALS, Globals, sync::Lrc};
use swc_ecma_ast::{EsVersion, Module, ModuleItem, Script};
use swc_ecma_codegen::{Config, Emitter, text_writer::JsWriter};
use swc_ecma_transforms_base::hygiene::hygiene;
use swc_ecma_visit::VisitMutWith;
use swc_ecma_parser::{EsSyntax, Syntax, parse_file_as_script};
use swc_tac::{rew::Options, module::TModule};

fn main() -> Result<()> {
    let path = std::env::args()
        .nth(1)
        .context("usage: swc-test-harness <file.js>")?;

    let js = compile_file(&path)?;
    print!("{js}");
    Ok(())
}

fn compile_file(path: &str) -> Result<String> {
    let cm: Lrc<SourceMap> = Lrc::new(SourceMap::default());
    let cm2 = cm.clone();

    GLOBALS.set(&Globals::default(), || compile_inner(path, cm, cm2))
}

fn compile_inner(path: &str, cm: Lrc<SourceMap>, cm_emit: Lrc<SourceMap>) -> Result<String> {
    // Parse as Script (no imports/exports — fixtures are plain scripts).
    let fm = cm
        .load_file(Path::new(path))
        .with_context(|| format!("failed to read {path}"))?;

    let mut errors = vec![];
    let script: Script = parse_file_as_script(
        &fm,
        Syntax::Es(EsSyntax::default()),
        EsVersion::Es2022,
        None,
        &mut errors,
    )
    .map_err(|e| anyhow::anyhow!("parse error: {e:?}"))?;

    if !errors.is_empty() {
        for e in &errors {
            eprintln!("parse warning: {e:?}");
        }
    }

    eprintln!("[harness] parsed {path}: {} top-level stmts", script.body.len());

    // Wrap Script stmts into a Module so CfgModule::try_from can consume it.
    let module = Module {
        span: script.span,
        body: script.body.into_iter().map(ModuleItem::Stmt).collect(),
        shebang: script.shebang,
    };

    // AST → CFG → TAC
    eprintln!("[harness] AST → CfgModule");
    let cfg_module = CfgModule::try_from(module).context("CfgModule conversion failed")?;
    eprintln!("[harness] CfgModule → TModule");
    let tmodule = TModule::try_from(cfg_module).context("TModule conversion failed")?;

    // TAC body → CFG → AST Function
    eprintln!("[harness] TModule.body → CFG Func (TAC→CFG rewrite)");
    let cfg_func =
        Options::bud(|opts| tmodule.body.to_func_with_options(opts))
            .context("TAC→CFG rewrite failed")?;

    eprintln!("[harness] CFG Func → SWC Function");
    let ast_fn: swc_ecma_ast::Function = cfg_func.into();
    let stmts = ast_fn.body.map(|b| b.stmts).unwrap_or_default();
    eprintln!("[harness] emitting {} stmts", stmts.len());

    // Reconstruct a Script, run hygiene to rename colliding temp vars, then emit.
    let mut out_script = Script {
        span: swc_common::DUMMY_SP,
        body: stmts,
        shebang: None,
    };

    out_script.visit_mut_with(&mut hygiene());

    let mut buf = vec![];
    {
        let wr = JsWriter::new(cm_emit.clone(), "\n", &mut buf, None);
        let mut emitter = Emitter {
            cfg: Config::default(),
            cm: cm_emit,
            comments: None,
            wr,
        };
        emitter
            .emit_script(&out_script)
            .context("codegen failed")?;
    }

    let inner = String::from_utf8(buf).context("codegen output was not valid UTF-8")?;
    // Wrap in IIFE so `return` statements (TAC terminators) are valid.
    Ok(format!("(function(){{\n{}}})();\n", inner))
}
