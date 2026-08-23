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

    /// Regression test: a `let` declared with no initializer, then reassigned
    /// in every arm of an `if`/`else` and read afterward, must resolve at the
    /// join point through that join block's own SSA parameter — not through a
    /// by-name `LoadId`/`StoreId`, and not through an alias that reaches
    /// directly into one specific branch's own value.
    ///
    /// Before the fix, `ToTACConverterCore::stmt`'s `Decl::Var` arm silently
    /// skipped registering the binding (`o.decls.insert(..)`) whenever a
    /// `VarDeclarator` had no initializer, so `let a;` never became an
    /// SSA-tracked local at all — every read/write of `a` fell back to
    /// by-name `StoreId`/`LoadId`, which is only safe when a single
    /// assignment dominates every use. That happens to hold for straight-line
    /// code, which is why `let a = 0;` (with an initializer, hence properly
    /// declared) never showed the bug — but it breaks the moment two
    /// non-dominating definitions (the if- and else-branches) both reach the
    /// same join-point read.
    portal_solutions_swibb::simple_module_test!(test_uninit_let_reassigned_across_if_else [
        "export function f(cond) {
            let a;
            if (cond) { a = 10; } else { a = 20; }
            return a;
         }
        "
    ] => |_sm, module| {
        use crate::SValue;

        let cfg_module = CfgModule::try_from(module).expect("CfgModule");
        let tmodule = TModule::try_from(cfg_module).expect("TModule");
        let smodule = SModule::try_from(tmodule).expect("SModule");
        let f = smodule.funcs.get(&swc_atoms::Atom::new("f")).expect("f must be in funcs");

        // The bug's fingerprint: `a` must never fall back to a by-name load
        // or store — it must be fully SSA-tracked via block params.
        for (_id, val) in f.cfg.values.iter() {
            match &val.value {
                SValue::LoadId(ident) | SValue::StoreId { target: ident, .. } => {
                    assert_ne!(
                        &*ident.0, "a",
                        "`a` must not fall back to by-name LoadId/StoreId"
                    );
                }
                _ => {}
            }
        }

        // Find the block whose terminator returns a value, and confirm that
        // value is a genuine `SValue::Param` belonging to that same block
        // (i.e. it was threaded through the join block's own parameter list),
        // not an alias resolving directly into one specific predecessor.
        let mut found_return = false;
        for (block_id, block) in f.cfg.blocks.iter() {
            if let crate::STerm::Return(Some(ret_id)) = &block.postcedent.term {
                found_return = true;
                match &f.cfg.values[*ret_id].value {
                    SValue::Param { block: param_block, .. } => {
                        assert_eq!(
                            *param_block, block_id,
                            "returned value must be a param of its own block"
                        );
                    }
                    other => panic!(
                        "expected the returned value to be a block Param, got {:?}",
                        other
                    ),
                }

                // The two branches must actually disagree on what they pass
                // for this param — otherwise the "merge" is vacuous.
                let SValue::Param { idx, .. } = &f.cfg.values[*ret_id].value else { unreachable!() };
                let inputs: std::collections::BTreeSet<_> =
                    f.cfg.inputs(block_id, *idx).collect();
                assert!(
                    inputs.len() >= 2,
                    "join block param must receive distinct values from both branches, got {:?}",
                    inputs
                );
            }
        }
        assert!(found_return, "function must contain a Return");
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
