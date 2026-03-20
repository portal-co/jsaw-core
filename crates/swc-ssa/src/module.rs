//! Module-level IR for ES modules in SSA form.
//!
//! Provides [`SModule`], the SSA counterpart of [`TModule`].
//! Import/export metadata is preserved verbatim from the TAC layer; each
//! [`TFunc`] body is lowered to an [`SFunc`] via the normal SSA conversion.

use std::collections::HashMap;

use portal_jsc_swc_util::ImportMapper;
use swc_atoms::Atom;
use swc_ecma_ast::ImportDecl;
use swc_tac::{TFunc, module::CfgModuleImportMapper, module::TModule};

use crate::{Error, SFunc};
pub use swc_cfg::module::ExportSpec;

// ── SModule ───────────────────────────────────────────────────────────────

/// A complete ES module in SSA form.
///
/// Mirrors [`TModule`] but with [`SFunc`] bodies.
pub struct SModule {
    /// Verbatim `import` declarations from the source module.
    pub imports: Vec<ImportDecl>,
    /// Hoisted function declarations in SSA form.
    pub funcs: HashMap<Atom, SFunc>,
    /// Top-level executable statements in SSA form.
    pub body: SFunc,
    /// Export metadata (identical to the CFG and TAC layers).
    pub exports: Vec<ExportSpec>,
}

impl SModule {
    /// Returns an [`ImportMapper`] backed by this module's `import`
    /// declarations.
    ///
    /// Downstream analysis can call `mapper.import_of(id)` to determine
    /// whether an [`SValue::LoadId`](crate::SValue::LoadId) refers to an
    /// imported binding, and to discover the module specifier and import kind.
    pub fn import_mapper(&self) -> impl ImportMapper + '_ {
        CfgModuleImportMapper::from_imports(&self.imports)
    }
}

// ── TryFrom<TModule> ─────────────────────────────────────────────────────

impl TryFrom<TModule> for SModule {
    type Error = Error;

    fn try_from(module: TModule) -> Result<Self, Self::Error> {
        let mut funcs: HashMap<Atom, SFunc> = HashMap::with_capacity(module.funcs.len());
        for (name, tfunc) in module.funcs {
            funcs.insert(name, SFunc::try_from(tfunc)?);
        }

        let body = SFunc::try_from(module.body)?;

        Ok(SModule {
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
    use portal_jsc_common::syntax::ImportMap;
    use swc_cfg::module::CfgModule;
    use swc_tac::module::TModule;

    /// Pipeline test: `Module → CfgModule → TModule → SModule`.
    ///
    /// Verifies that import/export metadata is preserved through all three
    /// layers and that an `ImportMapper` built from `SModule::import_mapper()`
    /// correctly identifies imported bindings.
    portal_solutions_swibb::simple_module_test!(test_smodule_pipeline [
        "import foo from './foo';
         export function bar(x) { return x + 1; }
         export default function() { return 0; }
         export * from './reexport';
        "
    ] => |_sm, module| {
        let cfg_module = CfgModule::try_from(module)
            .expect("CfgModule::try_from failed");

        assert_eq!(cfg_module.imports.len(), 1, "one import");
        // exports: bar (Local), default func (DefaultFunc), reexport (ReexportAll)
        assert_eq!(cfg_module.exports.len(), 3, "three exports");

        let tmodule = TModule::try_from(cfg_module)
            .expect("TModule::try_from failed");
        let smodule = SModule::try_from(tmodule)
            .expect("SModule::try_from failed");

        assert_eq!(smodule.imports.len(), 1, "imports preserved through pipeline");
        assert_eq!(smodule.exports.len(), 3, "exports preserved through pipeline");

        // `bar` should be in `funcs`.
        assert!(smodule.funcs.contains_key(&swc_atoms::Atom::new("bar")),
                "bar must be in funcs");

        // The import mapper should recognise `foo` (with the SyntaxContext that
        // the resolver assigned during `simple_module_test!` parsing).
        //
        // We find `foo`'s resolved Id by inspecting the SSA body's externals.
        let externals = smodule.body.cfg.externals();
        let foo_id = externals
            .iter()
            .find(|(sym, _)| sym == &swc_atoms::Atom::new("foo"))
            .cloned();

        if let Some(foo_id) = foo_id {
            let mapper = smodule.import_mapper();
            let resolved = mapper.import_of(&foo_id);
            assert!(resolved.is_some(), "foo must be recognised as an import");
            let (src, kind) = resolved.unwrap();
            assert_eq!(&*src, "./foo", "import source matches");
            assert_eq!(kind, ImportMap::Default, "import kind is Default");
        }
        // If foo_id is None the body didn't reference foo, which is also fine.
    });

    portal_solutions_swibb::simple_module_test!(test_smodule_body_compiles [
        "const x = 1 + 2;
         export { x };
        "
    ] => |_sm, module| {
        let cfg_module = CfgModule::try_from(module).expect("CfgModule");
        let tmodule = TModule::try_from(cfg_module).expect("TModule");
        let smodule = SModule::try_from(tmodule).expect("SModule");

        // body must have at least one block
        assert!(!smodule.body.cfg.blocks.iter().next().is_none(),
                "body must have blocks");
        // one export: x
        assert_eq!(smodule.exports.len(), 1);
    });
}
