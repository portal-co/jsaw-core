//! Module-level IR for ES modules.
//!
//! This module provides [`CfgModule`], a container that holds hoisted
//! import/export metadata alongside the function-level CFG IR for an ES
//! module's top-level executable statements.
//!
//! # Design
//!
//! Static `import`/`export` declarations are lifted out of the CFG and
//! stored as plain metadata.  The remaining executable top-level statements
//! become the module `body` [`Func`].  Hoisted function declarations
//! (`export function foo() {}`) are stored separately in `funcs`.

use std::collections::HashMap;

use swc_atoms::{Atom, Wtf8Atom};
use swc_common::{Span, SyntaxContext};
use swc_ecma_ast::{
    BindingIdent, ClassDecl, Decl, DefaultDecl, ExportSpecifier, Id, ImportDecl, ModuleDecl,
    ModuleExportName, ModuleItem, ObjectPatProp, Pat, Stmt, VarDecl, VarDeclKind, VarDeclarator,
};

use crate::{to_cfg::ToCfgConversionCtx, Cfg, Error, Func, Term};

// ── ExportSpec ───────────────────────────────────────────────────────────────

/// Describes one exported binding from an ES module.
///
/// This enum is shared across all three IR layers (`swc-cfg`, `swc-tac`,
/// `swc-ssa`), where the higher-level crates re-export it from here.
#[derive(Clone, Debug)]
pub enum ExportSpec {
    /// A binding that lives in this module's own scope.
    ///
    /// Covers `export const x = …`, `export class Foo {}`, and
    /// `export { x as y }` (no `from` clause).
    Local {
        /// The Id of the local binding.
        local: Id,
        /// The name under which it is exported.
        exported: Atom,
        /// Source span.
        span: Span,
    },

    /// `export default function foo() {}` — the function body is stored in
    /// `CfgModule::funcs` under `func_name`.
    DefaultFunc {
        /// Key into `CfgModule::funcs`.
        func_name: Atom,
    },

    /// `export default <expr>` or `export default class` — a synthetic
    /// `var *default* = <expr>` was emitted into `body`.
    DefaultExpr {
        /// Id of the synthetic `*default*` variable in `body`.
        local: Id,
    },

    /// `export { x as y } from 'mod'` — a pure re-export; no statements
    /// are added to `body`.
    ///
    /// Each entry in `names` is `(orig_name_in_source, exported_name)`.
    /// For `export { default as y } from 'mod'` the tuple is
    /// `("default", "y")`.
    Reexport {
        /// Module specifier of the re-exported module.
        source: Atom,
        /// `(original_name_in_source, exported_name_in_this_module)`.
        names: Vec<(Atom, Atom)>,
        /// Source span.
        span: Span,
    },

    /// `export * from 'mod'` or `export * as ns from 'mod'`.
    ReexportAll {
        /// Module specifier of the re-exported module.
        source: Atom,
        /// Present when `export * as ns from 'mod'` — the namespace alias.
        ns: Option<Atom>,
        /// Source span.
        span: Span,
    },
}

// ── CfgModule ─────────────────────────────────────────────────────────────

/// A complete ES module in CFG form.
///
/// Import/export declarations are hoisted out and stored as metadata.
/// The remaining top-level executable statements become `body`.
/// Hoisted function declarations (including `export default function`) are
/// stored in `funcs`.
#[derive(Clone)]
pub struct CfgModule {
    /// Verbatim `import` declarations — free variables in `body` and `funcs`.
    pub imports: Vec<ImportDecl>,
    /// Hoisted function declarations, keyed by their declared name.
    /// Also holds named and anonymous `export default function`.
    pub funcs: HashMap<Atom, Func>,
    /// Top-level executable statements expressed as a CFG function.
    /// Has no parameters and is neither async nor a generator.
    pub body: Func,
    /// Export metadata.
    pub exports: Vec<ExportSpec>,
}

// ── Helpers ───────────────────────────────────────────────────────────────

/// Convert a `Wtf8Atom` module specifier to a regular `Atom`.
///
/// Module specifiers are always valid UTF-8, but `Str.value` uses `Wtf8Atom`
/// to support the general case.  We use a lossy conversion (replacing any
/// malformed surrogates with U+FFFD) which is the same strategy used by the
/// SWC AST itself.
fn wtf8_to_atom(w: &Wtf8Atom) -> Atom {
    w.to_atom_lossy().into_owned()
}

fn module_export_name_atom(name: &ModuleExportName) -> Atom {
    name.atom().into_owned()
}

/// Build a module-body [`Func`] from a flat list of statements.
fn build_body(stmts: Vec<Stmt>) -> Result<Func, Error> {
    let mut cfg = Cfg::default();
    let entry = cfg.blocks.alloc(Default::default());
    let exit = ToCfgConversionCtx::default().transform_all(
        &mut cfg,
        &mut (),
        &stmts,
        entry,
        None,
    )?;
    cfg.blocks[exit].end.term = Term::Return(None);
    cfg.simplify();
    Ok(Func {
        cfg,
        entry,
        params: vec![],
        is_generator: false,
        is_async: false,
    })
}

/// Recursively collect every ident bound by `pat` and push a
/// `ExportSpec::Local` for each one.
fn collect_pat_exports(pat: &Pat, span: Span, exports: &mut Vec<ExportSpec>) {
    match pat {
        Pat::Ident(bi) => {
            exports.push(ExportSpec::Local {
                local: bi.id.clone().into(),
                exported: bi.id.sym.clone(),
                span,
            });
        }
        Pat::Array(a) => {
            for elem in a.elems.iter().flatten() {
                collect_pat_exports(elem, span, exports);
            }
        }
        Pat::Object(o) => {
            for prop in &o.props {
                match prop {
                    ObjectPatProp::KeyValue(kv) => {
                        collect_pat_exports(&kv.value, span, exports);
                    }
                    ObjectPatProp::Assign(a) => {
                        exports.push(ExportSpec::Local {
                            local: a.key.id.clone().into(),
                            exported: a.key.id.sym.clone(),
                            span,
                        });
                    }
                    ObjectPatProp::Rest(r) => {
                        collect_pat_exports(&r.arg, span, exports);
                    }
                }
            }
        }
        Pat::Rest(r) => collect_pat_exports(&r.arg, span, exports),
        Pat::Assign(a) => collect_pat_exports(&a.left, span, exports),
        Pat::Expr(_) | Pat::Invalid(_) => {}
    }
}

// ── TryFrom<Module> ──────────────────────────────────────────────────────

impl TryFrom<swc_ecma_ast::Module> for CfgModule {
    type Error = Error;

    fn try_from(module: swc_ecma_ast::Module) -> Result<Self, Self::Error> {
        let mut imports: Vec<ImportDecl> = Vec::new();
        let mut funcs: HashMap<Atom, Func> = HashMap::new();
        let mut exports: Vec<ExportSpec> = Vec::new();
        let mut body_stmts: Vec<Stmt> = Vec::new();

        for item in module.body {
            match item {
                // ── plain statement ─────────────────────────────────────
                ModuleItem::Stmt(s) => body_stmts.push(s),

                // ── module declaration ──────────────────────────────────
                ModuleItem::ModuleDecl(decl) => match decl {
                    // import …
                    ModuleDecl::Import(d) => imports.push(d),

                    // export { fn decl }
                    ModuleDecl::ExportDecl(e) => match e.decl {
                        Decl::Fn(f) => {
                            let span = f.function.span;
                            let sym = f.ident.sym.clone();
                            let id: Id = f.ident.clone().into();
                            funcs.insert(sym.clone(), Func::try_from(*f.function)?);
                            exports.push(ExportSpec::Local {
                                local: id,
                                exported: sym,
                                span,
                            });
                        }
                        Decl::Class(c) => {
                            let span = c.class.span;
                            let sym = c.ident.sym.clone();
                            let id: Id = c.ident.clone().into();
                            exports.push(ExportSpec::Local {
                                local: id,
                                exported: sym,
                                span,
                            });
                            body_stmts.push(Stmt::Decl(Decl::Class(c)));
                        }
                        Decl::Var(v) => {
                            let span = v.span;
                            for decl in &v.decls {
                                collect_pat_exports(&decl.name, span, &mut exports);
                            }
                            body_stmts.push(Stmt::Decl(Decl::Var(v)));
                        }
                        _ => {
                            return Err(Error::UnsupportedSyntax {
                                file: file!(),
                                line: line!(),
                            });
                        }
                    },

                    // export default …
                    ModuleDecl::ExportDefaultDecl(e) => match e.decl {
                        DefaultDecl::Fn(f) => {
                            let func_name = f
                                .ident
                                .as_ref()
                                .map(|i| i.sym.clone())
                                .unwrap_or_else(|| Atom::new("*default*"));
                            funcs.insert(func_name.clone(), Func::try_from(*f.function)?);
                            exports.push(ExportSpec::DefaultFunc { func_name });
                        }
                        DefaultDecl::Class(c) => {
                            let span = c.class.span;
                            let ident = c.ident.unwrap_or_else(|| {
                                swc_ecma_ast::Ident::new(
                                    Atom::new("*default*"),
                                    span,
                                    SyntaxContext::empty(),
                                )
                            });
                            let temp_id: Id = ident.clone().into();
                            exports.push(ExportSpec::DefaultExpr { local: temp_id });
                            body_stmts.push(Stmt::Decl(Decl::Class(ClassDecl {
                                ident,
                                declare: false,
                                class: c.class,
                            })));
                        }
                        DefaultDecl::TsInterfaceDecl(_) => {
                            return Err(Error::UnsupportedSyntax {
                                file: file!(),
                                line: line!(),
                            });
                        }
                    },

                    // export default <expr>
                    ModuleDecl::ExportDefaultExpr(e) => {
                        let span = e.span;
                        let temp_ident = swc_ecma_ast::Ident::new(
                            Atom::new("*default*"),
                            span,
                            SyntaxContext::empty(),
                        );
                        let temp_id: Id = temp_ident.clone().into();
                        // var *default* = <expr>
                        body_stmts.push(Stmt::Decl(Decl::Var(Box::new(VarDecl {
                            span,
                            ctxt: SyntaxContext::empty(),
                            kind: VarDeclKind::Var,
                            declare: false,
                            decls: vec![VarDeclarator {
                                span,
                                name: Pat::Ident(BindingIdent {
                                    id: temp_ident,
                                    type_ann: None,
                                }),
                                init: Some(e.expr),
                                definite: false,
                            }],
                        }))));
                        exports.push(ExportSpec::DefaultExpr { local: temp_id });
                    }

                    // export { … } or export { … } from '…'
                    ModuleDecl::ExportNamed(e) => {
                        let span = e.span;
                        match e.src {
                            // local re-exports / named local exports
                            None => {
                                for spec in e.specifiers {
                                    match spec {
                                        ExportSpecifier::Named(s) => {
                                            let local_id: Id = match &s.orig {
                                                ModuleExportName::Ident(i) => i.clone().into(),
                                                        ModuleExportName::Str(str_lit) => (
                                                    wtf8_to_atom(&str_lit.value),
                                                    SyntaxContext::empty(),
                                                ),
                                            };
                                            let local_sym = module_export_name_atom(&s.orig);
                                            let exported = s
                                                .exported
                                                .as_ref()
                                                .map(module_export_name_atom)
                                                .unwrap_or_else(|| local_sym);
                                            exports.push(ExportSpec::Local {
                                                local: local_id,
                                                exported,
                                                span,
                                            });
                                        }
                                        ExportSpecifier::Default(s) => {
                                            let sym = s.exported.sym.clone();
                                            exports.push(ExportSpec::Local {
                                                local: s.exported.into(),
                                                exported: sym,
                                                span,
                                            });
                                        }
                                        ExportSpecifier::Namespace(_) => {
                                            // `export * as ns` without a source is illegal JS
                                            return Err(Error::UnsupportedSyntax {
                                                file: file!(),
                                                line: line!(),
                                            });
                                        }
                                    }
                                }
                            }

                            // re-exports from another module
                            Some(src) => {
                                let source: Atom = wtf8_to_atom(&src.value);
                                let mut names: Vec<(Atom, Atom)> = Vec::new();
                                for spec in e.specifiers {
                                    match spec {
                                        ExportSpecifier::Named(s) => {
                                            let orig = module_export_name_atom(&s.orig);
                                            let exported = s
                                                .exported
                                                .as_ref()
                                                .map(module_export_name_atom)
                                                .unwrap_or_else(|| orig.clone());
                                            names.push((orig, exported));
                                        }
                                        ExportSpecifier::Default(s) => {
                                            names.push((
                                                Atom::new("default"),
                                                s.exported.sym.clone(),
                                            ));
                                        }
                                        ExportSpecifier::Namespace(s) => {
                                            // export * as ns from 'mod'
                                            let ns = module_export_name_atom(&s.name);
                                            exports.push(ExportSpec::ReexportAll {
                                                source: wtf8_to_atom(&src.value),
                                                ns: Some(ns),
                                                span,
                                            });
                                        }
                                    }
                                }
                                if !names.is_empty() {
                                    exports.push(ExportSpec::Reexport {
                                        source,
                                        names,
                                        span,
                                    });
                                }
                            }
                        }
                    }

                    // export * from '…'
                    ModuleDecl::ExportAll(e) => {
                        exports.push(ExportSpec::ReexportAll {
                            source: wtf8_to_atom(&e.src.value),
                            ns: None,
                            span: e.span,
                        });
                    }

                    // TypeScript-specific module-level declarations
                    ModuleDecl::TsImportEquals(_)
                    | ModuleDecl::TsExportAssignment(_)
                    | ModuleDecl::TsNamespaceExport(_) => {
                        return Err(Error::UnsupportedSyntax {
                            file: file!(),
                            line: line!(),
                        });
                    }
                },
            }
        }

        let body = build_body(body_stmts)?;
        Ok(CfgModule {
            imports,
            funcs,
            exports,
            body,
        })
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use swc_common::{Span, SyntaxContext};
    use swc_ecma_ast::{
        Ident, ImportDecl, ImportDefaultSpecifier, ImportSpecifier, Module, ModuleDecl, ModuleItem,
        Str,
    };

    fn dummy_span() -> Span {
        Span::dummy_with_cmt()
    }

    fn make_import(src: &str, local_name: &str) -> ImportDecl {
        ImportDecl {
            span: dummy_span(),
            specifiers: vec![ImportSpecifier::Default(ImportDefaultSpecifier {
                span: dummy_span(),
                local: Ident::new(
                    Atom::new(local_name),
                    dummy_span(),
                    SyntaxContext::empty(),
                ),
            })],
            src: Box::new(Str {
                span: dummy_span(),
                value: Atom::new(src).into(),
                raw: None,
            }),
            type_only: false,
            with: None,
            phase: Default::default(),
        }
    }

    #[test]
    fn test_imports_are_preserved() {
        swc_common::GLOBALS.set(&Default::default(), || {
            let module = Module {
                span: dummy_span(),
                body: vec![ModuleItem::ModuleDecl(ModuleDecl::Import(make_import(
                    "./foo", "foo",
                )))],
                shebang: None,
            };
            let cfg = CfgModule::try_from(module).unwrap();
            assert_eq!(cfg.imports.len(), 1);
            assert_eq!(&*cfg.imports[0].src.value, "./foo");
            assert!(cfg.exports.is_empty());
            assert!(cfg.funcs.is_empty());
        });
    }

    #[test]
    fn test_export_all_becomes_reexport_all() {
        use swc_ecma_ast::ExportAll;
        swc_common::GLOBALS.set(&Default::default(), || {
            let module = Module {
                span: dummy_span(),
                body: vec![ModuleItem::ModuleDecl(ModuleDecl::ExportAll(ExportAll {
                    span: dummy_span(),
                    src: Box::new(Str {
                        span: dummy_span(),
                        value: Atom::new("./bar").into(),
                        raw: None,
                    }),
                    with: None,
                    type_only: false,
                }))],
                shebang: None,
            };
            let cfg = CfgModule::try_from(module).unwrap();
            assert_eq!(cfg.exports.len(), 1);
            assert!(matches!(
                &cfg.exports[0],
                ExportSpec::ReexportAll { source, ns: None, .. } if source == &Atom::new("./bar")
            ));
        });
    }

    #[test]
    fn test_reexport_named() {
        use swc_ecma_ast::{ExportNamedSpecifier, ExportSpecifier, ModuleExportName, NamedExport};
        swc_common::GLOBALS.set(&Default::default(), || {
            let module = Module {
                span: dummy_span(),
                body: vec![ModuleItem::ModuleDecl(ModuleDecl::ExportNamed(NamedExport {
                    span: dummy_span(),
                    specifiers: vec![ExportSpecifier::Named(ExportNamedSpecifier {
                        span: dummy_span(),
                        orig: ModuleExportName::Ident(Ident::new(
                            Atom::new("x"),
                            dummy_span(),
                            SyntaxContext::empty(),
                        )),
                        exported: Some(ModuleExportName::Ident(Ident::new(
                            Atom::new("y"),
                            dummy_span(),
                            SyntaxContext::empty(),
                        ))),
                        is_type_only: false,
                    })],
                    src: Some(Box::new(Str {
                        span: dummy_span(),
                        value: Atom::new("./mod").into(),
                        raw: None,
                    })),
                    type_only: false,
                    with: None,
                }))],
                shebang: None,
            };
            let cfg = CfgModule::try_from(module).unwrap();
            assert_eq!(cfg.exports.len(), 1);
            match &cfg.exports[0] {
                ExportSpec::Reexport { source, names, .. } => {
                    assert_eq!(source, &Atom::new("./mod"));
                    assert_eq!(names.len(), 1);
                    assert_eq!(names[0].0, Atom::new("x"));
                    assert_eq!(names[0].1, Atom::new("y"));
                }
                other => panic!("expected Reexport, got {other:?}"),
            }
        });
    }
}
