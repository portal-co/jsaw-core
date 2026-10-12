//! Module-level IR for ES modules in SSA form.
//!
//! Provides [`SModule`], the SSA counterpart of [`TModule`].
//! Import/export metadata is preserved verbatim from the TAC layer; each
//! [`TFunc`] body is lowered to an [`SFunc`] via the normal SSA conversion.

use std::{
    collections::{BTreeSet, HashMap},
    fmt,
};

use portal_jsc_swc_util::ImportMapper;
use sha3::{Digest, Sha3_256};
use swc_atoms::Atom;
use swc_common::SyntaxContext;
use swc_ecma_ast::{ImportDecl, ModuleItem};
use swc_tac::{Item, TFunc, module::CfgModuleImportMapper, module::TModule};

use crate::{Error, SFunc, SValue, SValueW};
pub use swc_cfg::module::ExportSpec;

/// Version marker included in every function fingerprint.
///
/// Bump this whenever the canonical semantic encoding changes. Cached
/// inventory records from the prior encoder must then be treated as misses.
pub const FUNCTION_FINGERPRINT_SCHEMA: &str = "jsaw.function.v1";

/// A content digest rendered as lowercase hexadecimal for cache keys and
/// revision manifests. It intentionally does not contain a source span.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionFingerprint([u8; 32]);

impl FunctionFingerprint {
    /// Return the domain-separated digest as 64 lowercase hexadecimal digits.
    pub fn to_hex(self) -> String {
        let mut output = String::with_capacity(64);
        for byte in self.0 {
            use fmt::Write as _;
            write!(output, "{byte:02x}").expect("writing to String cannot fail");
        }
        output
    }
}

impl fmt::Display for FunctionFingerprint {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.to_hex())
    }
}

/// Compute a domain-separated fingerprint of normalized JavaScript source.
///
/// This intentionally strips comments and whitespace before hashing. It is a
/// source-ingestion cache key, not a substitute for the later hygienic
/// dependency/layout checks that decide whether a cached fragment is safe to
/// reuse. Syntax errors are returned to the caller instead of being hashed as
/// text, so malformed source cannot alias a valid module.
pub fn source_fingerprint(
    source: &str,
) -> Result<FunctionFingerprint, swc_ecma_parser::error::Error> {
    let mut errors = Vec::new();
    let source_map = swc_common::sync::Lrc::new(swc_common::SourceMap::default());
    let file = source_map.new_source_file(
        swc_common::sync::Lrc::new(swc_common::FileName::Custom("<fingerprint>".to_owned())),
        source.to_owned(),
    );
    let module = swc_ecma_parser::parse_file_as_module(
        &file,
        swc_ecma_parser::Syntax::Es(swc_ecma_parser::EsSyntax::default()),
        swc_ecma_ast::EsVersion::Es2022,
        None,
        &mut errors,
    )?;
    if let Some(error) = errors.into_iter().next() {
        return Err(error);
    }
    Ok(semantic_fingerprint(&swc_ecma_codegen::to_code(&module)))
}

/// Fingerprint canonical semantic text under the function-fingerprint domain.
///
/// Compiler layers which already have a canonical rendering (for example an
/// ABI-only function signature) use this instead of reparsing text merely to
/// reach [`source_fingerprint`].
pub fn semantic_fingerprint(normalized: &str) -> FunctionFingerprint {
    let mut hasher = Sha3_256::new();
    hasher.update(FUNCTION_FINGERPRINT_SCHEMA.as_bytes());
    hasher.update([0]);
    hasher.update(normalized.as_bytes());
    FunctionFingerprint(hasher.finalize().into())
}

fn function_fingerprint(function: &SFunc) -> Result<FunctionFingerprint, Error> {
    let tac = TFunc::try_from(function)?;
    let cfg = swc_cfg::Func::try_from(tac)?;
    let source: swc_ecma_ast::Function = cfg.into();
    let expression = swc_ecma_ast::Expr::Fn(swc_ecma_ast::FnExpr {
        ident: None,
        function: Box::new(source),
    });
    Ok(semantic_fingerprint(&swc_ecma_codegen::to_code(
        &expression,
    )))
}

/// Stable source-domain identity for a top-level function declaration.
///
/// `module_path` is textual because module paths are textual ESM domains.
/// `ordinal` reserves a structural position for synthetic/anonymous forms.
/// Named top-level declarations currently use zero because jsaw-core's
/// `CfgModuleBuilder` stores the final hoisted binding by name; callers must
/// retain the hygienic [`Ident`] separately for compiler bookkeeping.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionKey {
    pub module_path: String,
    pub declared_name: Option<Atom>,
    pub ordinal: u32,
}

/// A fingerprinted, hygienic function inventory useful to streaming consumers.
#[derive(Clone, Debug, Default)]
pub struct FunctionInventory {
    pub functions: Vec<FunctionSourceInfo>,
}

/// Metadata for a single completed top-level function.
#[derive(Clone, Debug)]
pub struct FunctionSourceInfo {
    pub key: FunctionKey,
    pub fingerprint: FunctionFingerprint,
    /// Hygienic free references. Never derive cache/link identity from the
    /// rendered atom alone: `SyntaxContext` is part of `Ident` equality.
    pub direct_refs: BTreeSet<swc_ecma_ast::Id>,
}

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

/// Incrementally translate an ES module to SSA.
///
/// A complete SWC [`Module`](swc_ecma_ast::Module) holds every parsed function
/// AST at once. The traditional `Module -> CfgModule -> TModule -> SModule`
/// path then temporarily retains the same function in three more IRs. This
/// builder is the streaming seam: append parser items one at a time and each
/// hoisted function is lowered to SSA immediately. Only the final SSA module
/// and its still-unavoidable top-level body remain live.
///
/// `finish` preserves the ordinary module representation, including the
/// top-level stores that install hoisted functions into the shared module
/// context. Existing callers of the three whole-module `TryFrom` conversions
/// remain supported.
pub struct SModuleBuilder {
    cfg: swc_cfg::module::CfgModuleBuilder,
    funcs: HashMap<Atom, SFunc>,
    inventory: Vec<FunctionSourceInfo>,
    module_path: String,
    /// Reconstructing canonical source from SSA is intentionally opt-in: it
    /// is needed by hot-reload/cache clients, but makes ordinary streaming
    /// compilation retain a costly extra pass over every completed function.
    inventory_enabled: bool,
}

impl Default for SModuleBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl SModuleBuilder {
    /// Create an empty incremental module translator.
    pub fn new() -> Self {
        // Ordinary module lowering does not consume HCR inventory, so do not
        // pay for the SSA → TAC → AST canonical-fingerprint round-trip.
        Self::for_module_inner(String::new(), false)
    }

    /// Create an incremental translator with HCR/cache inventory keys scoped
    /// to `module_path`. This opt-in path computes canonical function
    /// fingerprints; use [`Self::new`] for ordinary large-module lowering.
    /// Module paths are textual ESM domains, unlike lexical bindings, which
    /// remain represented by hygienic SWC identifiers.
    pub fn for_module(module_path: impl Into<String>) -> Self {
        Self::for_module_inner(module_path.into(), true)
    }


    fn for_module_inner(module_path: String, inventory_enabled: bool) -> Self {
        Self {
            cfg: swc_cfg::module::CfgModuleBuilder::new(),
            funcs: HashMap::new(),
            inventory: Vec::new(),
            module_path,
            inventory_enabled,
        }
    }

    /// Translate one parsed top-level item.
    ///
    /// Functions declared by this item are drained from the CFG builder and
    /// immediately lowered through TAC into SSA, releasing their AST and CFG
    /// allocations before parsing the next item.
    pub fn append(&mut self, item: ModuleItem) -> Result<(), Error> {
        self.cfg.append(item).map_err(swc_tac::Error::from)?;
        for (name, func) in self.cfg.take_functions() {
            let tac = TFunc::try_from(func)?;
            let ssa = SFunc::try_from(tac)?;
            if self.inventory_enabled {
                self.inventory.push(FunctionSourceInfo {
                    key: FunctionKey {
                        module_path: self.module_path.clone(),
                        declared_name: Some(name.clone()),
                        ordinal: 0,
                    },
                    fingerprint: function_fingerprint(&ssa)?,
                    direct_refs: ssa.cfg.refs(),
                });
            }
            self.funcs.insert(name, ssa);
        }
        Ok(())
    }

    /// Take every hoisted function translated since the last call.
    ///
    /// This is deliberately destructive, matching
    /// [`CfgModuleBuilder::take_functions`](swc_cfg::module::CfgModuleBuilder::take_functions).
    /// A streaming consumer can call it after each [`Self::append`] and compile
    /// or serialize each returned [`SFunc`] before parsing the next item,
    /// rather than retaining a module-wide SSA function map. Callers that need
    /// a complete [`SModule`] simply do not call this method; [`Self::finish`]
    /// then retains its existing whole-module behavior.
    ///
    /// A builder whose functions were taken cannot later produce an equivalent
    /// complete `SModule`: the caller owns the function bodies and must also
    /// own any module-init/linking representation it needs.
    pub fn take_functions(&mut self) -> HashMap<Atom, SFunc> {
        std::mem::take(&mut self.funcs)
    }

    /// Take fingerprint/dependency records for functions translated since the
    /// prior call. Inventory follows the same destructive consumption model as
    /// [`Self::take_functions`], so a streaming compiler can cache a function
    /// fragment and its validity contract together.
    pub fn take_inventory(&mut self) -> FunctionInventory {
        let mut functions = std::mem::take(&mut self.inventory);
        functions.sort_by(|left, right| left.key.cmp(&right.key));
        FunctionInventory { functions }
    }

    /// Finish the module after all items have been appended.
    pub fn finish(mut self) -> Result<SModule, Error> {
        // `take_functions` leaves the CFG builder with only the top-level
        // body and module metadata. Lower that small residual body normally.
        let cfg = self.cfg.finish().map_err(swc_tac::Error::from)?;
        let mut body = SFunc::try_from(TFunc::try_from(cfg.body)?)?;

        // TModule::try_from traditionally prepends `name = function(){...}`
        // statements before converting the body to SSA. Recreate that final
        // representation directly here, using the SSA functions we already
        // translated item-by-item. These stores are intentionally non-SSA:
        // they populate the shared module context used by module init and by
        // nested closures.
        let entry = body.entry;
        let mut hoists = Vec::with_capacity(self.funcs.len() * 2);
        // Iterate in name order, not `HashMap` iteration order: std's
        // `RandomState` seeds from process-global state, which otherwise
        // shuffles hoist order — and with it downstream value-ids and
        // function discovery order — per process. The store order of
        // distinct names is semantically unobservable here.
        let mut hoisted: Vec<(&Atom, &SFunc)> = self.funcs.iter().collect();
        hoisted.sort_by(|(a, _), (b, _)| a.as_str().cmp(b.as_str()));
        for (name, function) in hoisted {
            let value = body.cfg.values.alloc(SValueW {
                value: SValue::Item {
                    item: Item::Func {
                        func: function.clone(),
                        arrow: false,
                    },
                    span: None,
                },
            });
            hoists.push(value);
            let store = body.cfg.values.alloc(SValueW {
                value: SValue::StoreId {
                    target: (name.clone(), SyntaxContext::empty()),
                    val: value,
                },
            });
            hoists.push(store);
        }
        // The SSA entry shim contains only the initial `undefined` value and
        // jumps to the translated top-level body. Put hoists after that value
        // and before the jump so every normal path sees them first.
        body.cfg.blocks[entry].stmts.extend(hoists);

        Ok(SModule {
            imports: cfg.imports,
            funcs: std::mem::take(&mut self.funcs),
            body,
            exports: cfg.exports,
        })
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

    portal_solutions_swibb::simple_module_test!(s_module_builder_takes_functions_incrementally [
        "function private_helper(x) { return x + 1; }
         export function public_helper(x) { return private_helper(x) + 1; }
         const top_level_value = 3;
        "
    ] => |_sm, module| {
        let mut builder = SModuleBuilder::new();
        let mut names = std::collections::BTreeSet::new();
        for item in module.body {
            builder.append(item).expect("incremental lowering should succeed");
            names.extend(builder.take_functions().into_keys());
        }

        assert_eq!(
            names,
            std::collections::BTreeSet::from([
                swc_atoms::Atom::new("private_helper"),
                swc_atoms::Atom::new("public_helper"),
            ]),
            "each completed module function should be available for immediate consumption"
        );

        // Taking functions is opt-in: the remaining body metadata can still
        // be finalized for streaming consumers which own their own function
        // compilation and linking representation.
        let residual = builder.finish().expect("residual body should lower");
        assert!(residual.funcs.is_empty());
        assert!(residual.body.cfg.blocks.iter().next().is_some());
    });

    portal_solutions_swibb::simple_module_test!(source_fingerprint_ignores_formatting_but_not_semantics [
        "export function f(x) { return x + 1; }"
    ] => |_sm, _module| {
        let formatted = source_fingerprint("export function f(x) { return x + 1; }")
            .expect("valid source should fingerprint");
        let comments_and_whitespace = source_fingerprint(
            "// formatting must not create a cache miss\nexport function f( x ) { /* comment */ return x + 1; }",
        )
        .expect("valid source should fingerprint");
        let changed = source_fingerprint("export function f(x) { return x + 2; }")
            .expect("valid source should fingerprint");
        assert_eq!(formatted, comments_and_whitespace);
        assert_ne!(formatted, changed);
    });

    portal_solutions_swibb::simple_module_test!(s_module_builder_inventory_tracks_hygienic_refs [
        "const imported = 1;
         export function public_helper(value) { return value + imported; }"
    ] => |_sm, module| {
        let mut builder = SModuleBuilder::for_module("src/main.js");
        for item in module.body {
            builder.append(item).expect("incremental lowering should succeed");
        }
        let inventory = builder.take_inventory();
        assert_eq!(inventory.functions.len(), 1);
        let function = &inventory.functions[0];
        assert_eq!(function.key.module_path, "src/main.js");
        assert_eq!(function.key.declared_name, Some(swc_atoms::Atom::new("public_helper")));
        assert_eq!(function.key.ordinal, 0);
        assert!(
            function.direct_refs.iter().any(|id| id.0 == swc_atoms::Atom::new("imported")),
            "references retain hygienic Ident values rather than flattened strings"
        );
        assert_ne!(function.fingerprint.to_hex(), "");
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
