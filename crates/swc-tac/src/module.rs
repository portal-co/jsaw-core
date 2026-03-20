//! Module-level IR for ES modules in TAC form.
//!
//! Provides [`TModule`], the TAC counterpart of [`swc_cfg::module::CfgModule`].
//! Import/export metadata is preserved verbatim from the CFG layer; each
//! [`swc_cfg::Func`] is lowered to a [`TFunc`].
//!
//! The [`CfgModuleImportMapper`] type is also exported so that the SSA layer
//! can build an [`ImportMapper`] from the same import declarations.

use std::collections::HashMap;

use portal_jsc_common::syntax::ImportMap;
use portal_jsc_swc_util::ImportMapper;
use swc_atoms::{Atom, Wtf8Atom};
use swc_cfg::module::CfgModule;
use swc_ecma_ast::{Id as Ident, ImportDecl, ImportSpecifier, ModuleExportName};

use crate::{TFunc, mapped};
pub use swc_cfg::module::ExportSpec;

// ── CfgModuleImportMapper ────────────────────────────────────────────────

/// An [`ImportMapper`] built from the `import` declarations of a module.
///
/// This type is `pub` so that the SSA layer can reuse it via
/// `swc_tac::module::CfgModuleImportMapper`.
pub struct CfgModuleImportMapper {
    /// Maps each imported binding (by its resolved `Id`) to
    /// `(module_specifier, import_kind)`.
    map: std::collections::BTreeMap<Ident, (Wtf8Atom, ImportMap<Atom>)>,
}

impl CfgModuleImportMapper {
    /// Build a mapper from a slice of `import` declarations.
    pub fn from_imports(imports: &[ImportDecl]) -> Self {
        let mut map = std::collections::BTreeMap::new();
        for decl in imports {
            let source: Wtf8Atom = decl.src.value.clone().into();
            for spec in &decl.specifiers {
                match spec {
                    ImportSpecifier::Named(s) => {
                        // `import { orig as local }` or `import { local }`
                        let import_kind = match &s.imported {
                            Some(imported) => ImportMap::Named {
                                name: imported.atom().into_owned(),
                            },
                            None => ImportMap::Named {
                                name: s.local.sym.clone(),
                            },
                        };
                        map.insert(s.local.clone().into(), (source.clone(), import_kind));
                    }
                    ImportSpecifier::Default(s) => {
                        // `import local from '…'`
                        map.insert(
                            s.local.clone().into(),
                            (source.clone(), ImportMap::Default),
                        );
                    }
                    ImportSpecifier::Namespace(s) => {
                        // `import * as local from '…'`
                        map.insert(s.local.clone().into(), (source.clone(), ImportMap::Star));
                    }
                }
            }
        }
        Self { map }
    }
}

impl ImportMapper for CfgModuleImportMapper {
    fn import_of(&self, cx: &Ident) -> Option<(Wtf8Atom, ImportMap<Atom>)> {
        self.map.get(cx).cloned()
    }
}

// ── TModule ───────────────────────────────────────────────────────────────

/// A complete ES module in TAC form.
///
/// Mirrors [`CfgModule`] but with [`TFunc`] bodies.
pub struct TModule {
    /// Verbatim `import` declarations from the source module.
    pub imports: Vec<ImportDecl>,
    /// Hoisted function declarations in TAC form.
    pub funcs: HashMap<Atom, TFunc>,
    /// Top-level executable statements in TAC form.
    pub body: TFunc,
    /// Export metadata (identical to the CFG layer).
    pub exports: Vec<ExportSpec>,
}

impl TModule {
    /// Returns an [`ImportMapper`] backed by this module's `import`
    /// declarations.
    ///
    /// The mapper is inexpensive to create and may be passed to any API that
    /// takes `&dyn ImportMapper`.
    pub fn import_mapper(&self) -> impl ImportMapper + '_ {
        CfgModuleImportMapper::from_imports(&self.imports)
    }
}

// ── TryFrom<CfgModule> ───────────────────────────────────────────────────

impl TryFrom<CfgModule> for TModule {
    type Error = crate::Error;

    fn try_from(module: CfgModule) -> Result<Self, Self::Error> {
        // Convert each hoisted Func to TFunc.
        let mut funcs: HashMap<Atom, TFunc> = HashMap::with_capacity(module.funcs.len());
        for (name, func) in module.funcs {
            let tfunc = mapped(|m| TFunc::try_from_with_mapper(&func, m))?;
            funcs.insert(name, tfunc);
        }

        // Convert the module body Func to TFunc.
        let mut body = mapped(|m| TFunc::try_from_with_mapper(&module.body, m))?;

        // Hoist function declarations into the entry block of `body`, mirroring
        // the treatment of `Decl::Fn` in `ToTACConverterCore::stmt`.
        //
        // We prepend (in declaration order) so that all hoisted functions are
        // visible to subsequent top-level code, matching JavaScript hoisting
        // semantics.
        use swc_common::SyntaxContext;
        let hoist_stmts: Vec<crate::TStmt> = funcs
            .iter()
            .map(|(name, tfunc)| crate::TStmt {
                left: crate::LId::Id {
                    id: (name.clone(), SyntaxContext::empty()),
                },
                flags: crate::ValFlags::SSA_LIKE,
                right: crate::Item::Func {
                    func: tfunc.clone(),
                    arrow: false,
                },
                span: swc_common::DUMMY_SP,
            })
            .collect();

        // Prepend at the start of the entry block.
        let entry = body.entry;
        let existing = std::mem::take(&mut body.cfg.blocks[entry].stmts);
        body.cfg.blocks[entry].stmts = hoist_stmts;
        body.cfg.blocks[entry].stmts.extend(existing);

        Ok(TModule {
            imports: module.imports,
            funcs,
            body,
            exports: module.exports,
        })
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use swc_atoms::Atom;
    use swc_cfg::module::CfgModule;
    use swc_common::{Span, SyntaxContext};
    use swc_ecma_ast::{Module, ModuleItem, ModuleDecl};

    /// Build a trivial CfgModule with one import and one re-export-all,
    /// then verify that TModule conversion succeeds and metadata is preserved.
    #[test]
    fn test_tmodule_imports_and_exports_preserved() {
        swc_common::GLOBALS.set(&Default::default(), || {
            use swc_ecma_ast::{
                ExportAll, ImportDecl, ImportDefaultSpecifier, ImportSpecifier, Str,
            };

            let dummy = Span::dummy_with_cmt();

            let import = ImportDecl {
                span: dummy,
                specifiers: vec![ImportSpecifier::Default(ImportDefaultSpecifier {
                    span: dummy,
                    local: swc_ecma_ast::Ident::new(
                        Atom::new("foo"),
                        dummy,
                        SyntaxContext::empty(),
                    ),
                })],
                src: Box::new(Str {
                    span: dummy,
                    value: Atom::new("./foo").into(),
                    raw: None,
                }),
                type_only: false,
                with: None,
                phase: Default::default(),
            };

            let export_all = ExportAll {
                span: dummy,
                src: Box::new(Str {
                    span: dummy,
                    value: Atom::new("./bar").into(),
                    raw: None,
                }),
                with: None,
                type_only: false,
            };

            let module = Module {
                span: dummy,
                body: vec![
                    ModuleItem::ModuleDecl(ModuleDecl::Import(import)),
                    ModuleItem::ModuleDecl(ModuleDecl::ExportAll(export_all)),
                ],
                shebang: None,
            };

            let cfg_module = CfgModule::try_from(module).expect("CfgModule::try_from failed");
            let tmodule = TModule::try_from(cfg_module).expect("TModule::try_from failed");

            assert_eq!(tmodule.imports.len(), 1, "one import preserved");
            assert_eq!(tmodule.exports.len(), 1, "one export-all preserved");

            // Verify the import mapper is usable.
            let mapper = tmodule.import_mapper();
            let unknown = mapper.import_of(&(Atom::new("__no_such__"), SyntaxContext::empty()));
            assert!(unknown.is_none(), "unknown binding returns None");

            // Verify the mapper recognises the default import of `foo`.
            // After the resolver runs, `foo` gets a non-empty SyntaxContext; here
            // we built the AST directly so SyntaxContext is empty.
            let known = mapper.import_of(&(Atom::new("foo"), SyntaxContext::empty()));
            assert!(known.is_some(), "foo should be recognised as an import");
            let (src, kind) = known.unwrap();
            assert_eq!(&*src, "./foo");
            assert_eq!(kind, ImportMap::Default);
        });
    }
}
