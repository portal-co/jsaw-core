use std::collections::{BTreeMap, BTreeSet, HashMap};

use anyhow::{bail, Context, Result};
use swc_atoms::Atom;
use swc_cfg::module::ExportSpec;
use swc_common::{sync::Lrc, FileName, Globals, Mark, SourceMap, SyntaxContext, GLOBALS};
use swc_ecma_ast::{
    EsVersion, ExportAll, ExportNamedSpecifier, ExportSpecifier, FnDecl, Module, ModuleDecl,
    ModuleExportName, ModuleItem, NamedExport,
};
use swc_ecma_codegen::{text_writer::JsWriter, Config, Emitter};
use swc_ecma_parser::{parse_file_as_module, EsSyntax, Syntax};
use swc_ecma_transforms_base::{hygiene::hygiene, resolver};
use swc_ecma_visit::VisitMutWith;
use swc_tac::{module::TModule, rew::Options};

use crate::passes::OptimizationPlan;

/// A correct whole-module resolver-backed adapter used until the incremental
/// resolver seam exists. It intentionally does not claim source streaming.
pub struct BufferedModulePipeline<'a> {
    plan: &'a OptimizationPlan,
}

impl<'a> BufferedModulePipeline<'a> {
    pub const fn new(plan: &'a OptimizationPlan) -> Self {
        Self { plan }
    }

    pub fn optimize_source(&self, source_name: &str, source: &str) -> Result<String> {
        let source_map: Lrc<SourceMap> = Lrc::new(SourceMap::default());
        let source_file = source_map.new_source_file(
            Lrc::new(FileName::Custom(source_name.to_owned())),
            source.to_owned(),
        );
        let mut parse_errors = Vec::new();
        let mut module = parse_file_as_module(
            &source_file,
            Syntax::Es(EsSyntax::default()),
            EsVersion::Es2022,
            None,
            &mut parse_errors,
        )
        .map_err(|error| anyhow::anyhow!("parse error in {source_name}: {error:?}"))?;
        if let Some(error) = parse_errors.into_iter().next() {
            bail!("parse error in {source_name}: {error:?}");
        }

        GLOBALS.set(&Globals::default(), || {
            module.visit_mut_with(&mut resolver(Mark::new(), Mark::new(), false));
            self.optimize_module(module)
                .and_then(|module| emit_module(&source_map, module))
        })
    }

    fn optimize_module(&self, module: Module) -> Result<Module> {
        let default_exports = module
            .body
            .iter()
            .filter_map(|item| match item {
                ModuleItem::ModuleDecl(
                    declaration @ (ModuleDecl::ExportDefaultExpr(_)
                    | ModuleDecl::ExportDefaultDecl(_)),
                ) => Some(declaration.clone()),
                _ => None,
            })
            .collect();
        // Resolution is deliberately whole-module, but every completed
        // function below is lowered and optimized as soon as the incremental
        // CFG builder releases it. CFG/TAC/SSA versions of a completed
        // function therefore do not accumulate with following functions.
        let mut cfg_builder = swc_cfg::module::CfgModuleBuilder::new();
        let mut functions = HashMap::new();
        for item in module.body {
            cfg_builder
                .append(item)
                .context("AST to CFG module conversion failed")?;
            for (name, cfg_function) in cfg_builder.take_functions() {
                let mut function = swc_tac::TFunc::try_from(cfg_function)
                    .with_context(|| format!("CFG to TAC conversion failed for `{name}`"))?;
                optimize_function(&mut function, self.plan)?;
                functions.insert(name, function);
            }
        }
        let cfg = cfg_builder
            .finish()
            .context("finishing CFG module failed")?;
        let mut body = swc_tac::TFunc::try_from(cfg.body)
            .context("CFG to TAC module-body conversion failed")?;
        optimize_function(&mut body, self.plan)?;
        ModuleEmitter::new(
            TModule {
                imports: cfg.imports,
                funcs: functions,
                body,
                exports: cfg.exports,
            },
            default_exports,
        )
        .emit()
    }
}

fn optimize_function(function: &mut swc_tac::TFunc, plan: &OptimizationPlan) -> Result<()> {
    run_tac_passes(function, plan, false);

    let mut ssa =
        swc_ssa::SFunc::try_from(function.clone()).context("TAC to SSA conversion failed")?;
    let rounds = plan
        .ordered()
        .filter_map(|pass| plan.intensity_for(pass))
        .map(|intensity| intensity.fixed_point_cap())
        .max()
        .unwrap_or(1);
    for _ in 0..rounds {
        if plan.contains("ssa.const-propagate") {
            ssa.cfg.do_consts(plan.semantic());
        }
        if plan.contains("ssa.simplify-conditions") {
            ssa.cfg.simplify_conditions();
        }
        if plan.contains("ssa.simplify-loads") {
            ssa.cfg.simplify_loads();
        }
        if plan.contains("ssa.simplify-justs") {
            ssa.cfg.simplify_justs();
        }
    }
    if plan.contains("ssa.equate-items") {
        ssa.cfg.equate_items();
    }
    if plan.contains("ssa.strip-useless") {
        ssa.cfg.strip_useless();
    }
    if plan.contains("ssa.inline-iifes") {
        ssa.cfg.inline_iifes();
    }

    let externals = function.cfg.externs().collect::<BTreeSet<_>>();
    let mut rewritten = ssa
        .try_into_with_prefix(Atom::new("__jsaw_opt"))
        .context("SSA to TAC conversion failed")?;
    // SSA rewriting introduces its own TAC temporaries, but imported/free
    // bindings retain their original names and must not become local `var`s.
    rewritten.cfg.decls.retain(|name| !externals.contains(name));
    *function = rewritten;
    run_tac_passes(function, plan, true);
    Ok(())
}

fn run_tac_passes(function: &mut swc_tac::TFunc, plan: &OptimizationPlan, after_ssa: bool) {
    if plan.contains("tac.simplify-justs") {
        let pass = crate::passes::descriptors()
            .iter()
            .copied()
            .find(|pass| pass.name == "tac.simplify-justs")
            .expect("registered TAC pass");
        for _ in 0..plan.fixed_point_cap(pass) {
            function.cfg.simplify_justs();
        }
    }
    if after_ssa && plan.contains("tac.strip-useless") {
        function.cfg.strip_useless();
    }
    function.cfg.update();
}

struct ModuleEmitter {
    module: TModule,
    default_exports: Vec<ModuleDecl>,
}

impl ModuleEmitter {
    fn new(module: TModule, default_exports: Vec<ModuleDecl>) -> Self {
        Self {
            module,
            default_exports,
        }
    }

    fn emit(mut self) -> Result<Module> {
        let mut body = Vec::new();
        body.extend(
            self.module
                .imports
                .drain(..)
                .map(|import| ModuleItem::ModuleDecl(ModuleDecl::Import(import))),
        );

        let function_contexts = exported_function_contexts(&self.module.exports);
        let function_names = self.module.funcs.keys().cloned().collect::<Vec<_>>();
        for name in function_names {
            let function = self
                .module
                .funcs
                .remove(&name)
                .expect("function name was collected from this map");
            let cfg_function = Options::bud(|options| function.to_func_with_options(options))
                .with_context(|| format!("rewriting function `{name}` from TAC to CFG failed"))?;
            let function = cfg_function.into();
            body.push(ModuleItem::Stmt(swc_ecma_ast::Stmt::Decl(
                swc_ecma_ast::Decl::Fn(FnDecl {
                    ident: swc_ecma_ast::Ident::new(
                        name.clone(),
                        swc_common::DUMMY_SP,
                        function_contexts
                            .get(&name)
                            .copied()
                            .unwrap_or_else(SyntaxContext::empty),
                    ),
                    declare: false,
                    function: Box::new(function),
                }),
            )));
        }

        // `TModule::try_from` installs hoisted functions into its synthetic
        // module body. The declarations above already represent those bindings,
        // so do not emit the synthetic body when it contains only those stores.
        if self.module.body.cfg.blocks[self.module.body.entry]
            .stmts
            .is_empty()
        {
            body.extend(
                tac_body_to_statements(&self.module.body)?
                    .into_iter()
                    .map(ModuleItem::Stmt),
            );
        }
        body.extend(exports_to_items(
            &self.module.exports,
            &mut self.default_exports.into_iter(),
        )?);
        Ok(Module {
            span: swc_common::DUMMY_SP,
            body,
            shebang: None,
        })
    }
}

fn tac_body_to_statements(function: &swc_tac::TFunc) -> Result<Vec<swc_ecma_ast::Stmt>> {
    let cfg_function = Options::bud(|options| function.to_func_with_options(options))
        .context("rewriting module body from TAC to CFG failed")?;
    let function: swc_ecma_ast::Function = cfg_function.into();
    Ok(function.body.map_or_else(Vec::new, |body| body.stmts))
}

fn exported_function_contexts(exports: &[ExportSpec]) -> BTreeMap<Atom, SyntaxContext> {
    exports
        .iter()
        .filter_map(|export| match export {
            ExportSpec::Local { local, .. } => Some((local.0.clone(), local.1)),
            _ => None,
        })
        .collect()
}

fn exports_to_items(
    exports: &[ExportSpec],
    default_exports: &mut impl Iterator<Item = ModuleDecl>,
) -> Result<Vec<ModuleItem>> {
    let mut local_specifiers = Vec::new();
    let mut items = Vec::new();

    for export in exports {
        match export {
            ExportSpec::Local {
                local,
                exported,
                span,
            } => {
                local_specifiers.push(ExportSpecifier::Named(ExportNamedSpecifier {
                    span: *span,
                    orig: ident_export_name(local),
                    exported: Some(atom_export_name(exported.clone())),
                    is_type_only: false,
                }));
            }
            ExportSpec::DefaultFunc { func_name } => {
                let declaration = default_exports
                    .next()
                    .context("missing original default function declaration")?;
                match declaration {
                    ModuleDecl::ExportDefaultDecl(mut declaration) => {
                        if let swc_ecma_ast::DefaultDecl::Fn(function) = &mut declaration.decl {
                            function.ident = Some(swc_ecma_ast::Ident::new(
                                func_name.clone(),
                                swc_common::DUMMY_SP,
                                SyntaxContext::empty(),
                            ));
                        }
                        items.push(ModuleItem::ModuleDecl(ModuleDecl::ExportDefaultDecl(
                            declaration,
                        )));
                    }
                    _ => bail!("default function export did not retain its declaration"),
                }
            }
            ExportSpec::DefaultExpr { .. } => {
                let declaration = default_exports
                    .next()
                    .context("missing original default export declaration")?;
                items.push(ModuleItem::ModuleDecl(declaration));
            }
            ExportSpec::Reexport {
                source,
                names,
                span,
                with,
            } => {
                items.push(ModuleItem::ModuleDecl(ModuleDecl::ExportNamed(
                    NamedExport {
                        span: *span,
                        specifiers: names
                            .iter()
                            .map(|(orig, exported)| {
                                ExportSpecifier::Named(ExportNamedSpecifier {
                                    span: *span,
                                    orig: atom_export_name(orig.clone()),
                                    exported: Some(atom_export_name(exported.clone())),
                                    is_type_only: false,
                                })
                            })
                            .collect(),
                        src: Some(Box::new(string_literal(source.clone(), *span))),
                        type_only: false,
                        with: with.clone(),
                    },
                )));
            }
            ExportSpec::ReexportAll {
                source,
                ns,
                span,
                with,
            } => {
                if let Some(namespace) = ns {
                    items.push(ModuleItem::ModuleDecl(ModuleDecl::ExportNamed(
                        NamedExport {
                            span: *span,
                            specifiers: vec![ExportSpecifier::Namespace(
                                swc_ecma_ast::ExportNamespaceSpecifier {
                                    span: *span,
                                    name: atom_export_name(namespace.clone()),
                                },
                            )],
                            src: Some(Box::new(string_literal(source.clone(), *span))),
                            type_only: false,
                            with: with.clone(),
                        },
                    )));
                } else {
                    items.push(ModuleItem::ModuleDecl(ModuleDecl::ExportAll(ExportAll {
                        span: *span,
                        src: Box::new(string_literal(source.clone(), *span)),
                        with: with.clone(),
                        type_only: false,
                    })));
                }
            }
        }
    }

    if !local_specifiers.is_empty() {
        items.insert(
            0,
            ModuleItem::ModuleDecl(ModuleDecl::ExportNamed(NamedExport {
                span: swc_common::DUMMY_SP,
                specifiers: local_specifiers,
                src: None,
                type_only: false,
                with: None,
            })),
        );
    }
    Ok(items)
}

fn ident_export_name(id: &swc_ecma_ast::Id) -> ModuleExportName {
    ModuleExportName::Ident(swc_ecma_ast::Ident::new(
        id.0.clone(),
        swc_common::DUMMY_SP,
        id.1,
    ))
}

fn atom_export_name(atom: Atom) -> ModuleExportName {
    ModuleExportName::Ident(swc_ecma_ast::Ident::new(
        atom,
        swc_common::DUMMY_SP,
        SyntaxContext::empty(),
    ))
}

fn string_literal(value: Atom, span: swc_common::Span) -> swc_ecma_ast::Str {
    swc_ecma_ast::Str {
        span,
        value: value.into(),
        raw: None,
    }
}

fn emit_module(source_map: &Lrc<SourceMap>, mut module: Module) -> Result<String> {
    module.visit_mut_with(&mut hygiene());
    let mut bytes = Vec::new();
    {
        let writer = JsWriter::new(source_map.clone(), "\n", &mut bytes, None);
        let mut emitter = Emitter {
            cfg: Config::default(),
            cm: source_map.clone(),
            comments: None,
            wr: writer,
        };
        emitter
            .emit_module(&module)
            .context("module code generation failed")?;
    }
    String::from_utf8(bytes).context("generated JavaScript was not UTF-8")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{cli::Cli, passes::build_plan};
    use clap::Parser;

    #[test]
    fn module_roundtrip_preserves_imports_exports_and_body() {
        let cli = Cli::try_parse_from(["jsaw-opt", "fixture.mjs"]).unwrap();
        let plan = build_plan(&cli).unwrap();
        let output = BufferedModulePipeline::new(&plan)
            .optimize_source(
                "fixture.mjs",
                "import value from './dep.mjs'; export function add(x) { return x + value; } export { add as renamed }; export default add;",
            )
            .unwrap();
        assert!(output.contains("from './dep.mjs'"));
        assert!(output.contains("export"));
        assert!(output.contains("function add"));
    }
}
