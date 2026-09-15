# Optimization CLI Plan

## Goal

Add a `jsaw-opt` binary that accepts one ECMAScript module, lowers each function through TAC and SSA, applies an explicitly selected set of optimization passes at the appropriate IR layer, and emits a complete optimized ECMAScript module. The default invocation must enable every pass that has been reviewed as fully semantics-preserving under standard ECMAScript semantics; it must not silently enable passes that rely on `SemanticFlags` assumptions or intentionally remove code.

```text
input module
  → streaming module ingestion / hygiene resolution
  → CFG function
  → TAC function ── selected TAC passes ──┐
  → SSA function ── selected SSA passes ──┤ per function, including nested functions
  → TAC function ── selected TAC cleanup ─┘
  → reconstructed output module
  → JavaScript source at --output
```

The command is an optimizer, not a bundler or a minifier: imports, exports, module evaluation semantics, and source-level JavaScript semantics remain intact. Formatting and generated temporary names may differ.

## Current repository seams and gaps

- `swc_cfg::module::CfgModuleBuilder` already accepts `ModuleItem`s incrementally and can drain completed hoisted `Func`s with `take_functions()`.
- `swc_ssa::module::SModuleBuilder` proves the intended memory seam: it drains a function and lowers it promptly, instead of retaining CFG, TAC, and SSA versions together. Its result is SSA-only, however, so it cannot be the CLI's final representation because `swc_ssa::rew::SFunc::try_into_with_prefix` is the supported route back to TAC.
- Existing conversions cover `CFG → TAC` (`TFunc::try_from`), `TAC → SSA` (`SFunc::try_from`), `SSA → TAC` (`SFunc::try_into_with_prefix`), `TAC → CFG` (`TFunc::to_func_with_options`), and `CFG → SWC Function`. The test harness only reconstructs a script body; it does not re-emit imports or exports.
- `CfgModule`, `TModule`, and `SModule` preserve imports and `ExportSpec`, but there is no inverse module renderer. `TModule.funcs` is a `HashMap`, so it also does not retain declaration order needed for deterministic output.
- SWC lexical identity is `swc_ecma_ast::Id` / `(Atom, SyntaxContext)`. The new code must retain and compare complete IDs for bindings; it must never key binding maps or membership sets by rendered identifier text.
- SWC's public resolver is a whole-module visitor. Parsing `parse_module_item()` one item at a time is possible, but simply resolving each item independently would break imports, shadowing, forward references, and top-level hoisting. Streaming must therefore include a module-scoped hygiene solution rather than treating raw `Atom`s as bindings.

## Decisions

1. Create a dedicated workspace package, `crates/portal-jsc-optimizer`, whose published package name is `portal-jsc-optimizer` and whose binary is `jsaw-opt`. Do not turn `swc-test-harness` into the product CLI.
2. Make the CLI module-only. Parse with `Syntax::Es(EsSyntax::default())` and `parse_module_item`; reject TypeScript until a separately tested `--syntax typescript` mode exists. Do not accept scripts and wrap them in an IIFE, unlike the test harness.
3. Treat streaming as bounded **intermediate-representation** retention: once a function's item is hygienically resolved, lower, optimize, and retain only its final TAC form plus compact module metadata. The final output module necessarily owns the optimized functions and top-level body.
4. Add a module-scoped streaming resolver before making the CLI claim fully streaming. Until it exists, the CLI may use a correct whole-module parse-and-resolve compatibility adapter, clearly documented as buffered rather than streaming. It must not ship as the advertised streaming implementation.
5. Centralize pass names, safety classification, layer, intensity support, defaults, ordering, and execution in one registry. Argument parsing and pipeline code must not independently match pass-name strings.
6. Passes disabled by default remain available only when explicitly requested and, where applicable, when the caller also supplies the necessary semantic assumptions. `clean_func` is not an ordinary optimization pass: it removes `trim()`/burnt branches and is excluded from this CLI's default registry.

## CLI interface

Use `clap` with derive support. Add `clap = { version = "4", features = ["derive"] }` to workspace dependencies and consume it only in the new CLI package. Keep `anyhow` for contextual process errors.

```text
jsaw-opt [OPTIONS] <INPUT>

Arguments:
  <INPUT>                         Input ECMAScript module path; `-` reads stdin

Options:
  -o, --output <PATH>             Output module path; `-` writes stdout [default: -]
      --pass <NAME>               Enable exactly one pass; repeat or use comma-separated names
      --passes <LIST>             Comma-separated replacement for the default pass set
      --exclude-pass <NAME>       Remove a pass from the resulting selected set; repeatable
      --intensity <LEVEL>         default | conservative | standard | aggressive [default: standard]
      --pass-intensity <P=L>      Per-pass intensity override; repeatable
      --semantic-flag <FLAG>      Required nonstandard semantic assumption; repeatable
      --list-passes               Print stable pass metadata and exit
      --check                     Optimize and validate, but do not write output
      --emit-ir <DIR>             Debug-only per-function TAC/SSA snapshots; not an output contract
      --syntax <KIND>             Initially only `ecmascript` [default: ecmascript]
  -h, --help
```

Rules:

- No `--pass`/`--passes` means the default safe set. Supplying either selects **only** named passes; users who want defaults plus a pass use `--exclude-pass` sparingly or name the full list deliberately. This avoids accidental activation of experimental passes as the registry grows.
- Parse comma-separated and repeated selection options into a `BTreeSet<PassName>` so duplicate spelling does not rerun a pass. Preserve registry order—not user argument order—for execution.
- Validate unknown names, duplicate/conflicting per-pass intensities, `--pass-intensity` for an unselected pass, and an unavailable intensity before reading or writing the output path. `--list-passes` performs no input I/O.
- `--intensity` sets only the intensity of passes that declare intensity support. A selected fixed-strength pass ignores the global level; report this in `--list-passes` and include the effective configuration in diagnostics.
- `aggressive` changes budgets/iterations only. It never changes the selected pass set or permits semantic assumptions. Assumption-based optimization requires a specific `--semantic-flag`, validated against the pass descriptor.
- Write to a temporary file in the destination directory and atomically rename it only after parse, lowering, optimization, re-emission, code generation, and validation all succeed. For stdout, buffer output and write only after success. Refuse input and output resolving to the same file unless the atomic-output implementation makes that explicitly safe.

Examples:

```bash
# Fully semantics-preserving defaults, reading stdin and writing stdout.
jsaw-opt -o - < input.mjs > output.mjs

# Run only canonical aliases and unused-value removal at a larger fixed-point budget.
jsaw-opt input.mjs -o output.mjs \
  --passes ssa.simplify-justs,ssa.strip-useless \
  --pass-intensity ssa.simplify-justs=aggressive

# Inspect the registry and its safety/default status.
jsaw-opt --list-passes
```

## Pass registry and initial policy

Add `crates/portal-jsc-optimizer/src/passes.rs`. Its public interface should be small:

```rust
pub struct OptimizationPlan { /* validated ordered selections */ }
pub struct PassDescriptor { /* name, layer, safety, intensity support, help */ }

pub fn descriptors() -> &'static [PassDescriptor];
pub fn build_plan(cli: &Cli) -> Result<OptimizationPlan, CliError>;
pub fn optimize_tac(func: &mut TFunc, plan: &OptimizationPlan, context: &PassContext) -> Result<()>;
pub fn optimize_ssa(func: &mut SFunc, plan: &OptimizationPlan, context: &PassContext) -> Result<()>;
```

`PassContext` owns the effective `SemanticCfg`, the immutable import mapper where a TAC transformation needs it, and a hygienic function identity used only for diagnostics and generated prefix allocation. It is the module's internal seam: callers select a plan once and never dispatch individual transformations themselves.

Initial descriptors:

| Stable name | Layer | Default | Intensity | Implementation/status |
|---|---|---:|---|---|
| `tac.simplify-justs` | TAC | yes | fixed-point cap | Existing `TCfg::simplify_justs`; aliases only. |
| `tac.strip-useless` | TAC | yes, after SSA re-emission | none | Existing `TCfg::strip_useless`; only removes literal/function/undefined definitions proved unreferenced by its analysis. Add differential tests before defaulting it. |
| `ssa.const-propagate` | SSA | yes | fixed-point cap | Existing `SCfg::do_consts(&SemanticCfg)`. With default empty flags, it must be limited to standard-semantics folds. |
| `ssa.simplify-conditions` | SSA | yes | fixed-point cap | Existing `SCfg::simplify_conditions`. |
| `ssa.simplify-loads` | SSA | yes | fixed-point cap | Existing `SCfg::simplify_loads`; its side-effect barrier is part of its correctness contract. |
| `ssa.simplify-justs` | SSA | yes | fixed-point cap | Existing `SCfg::simplify_justs`. |
| `ssa.equate-items` | SSA | no initially | none | Existing `SCfg::equate_items`; enable by default only after roundtrip/differential coverage proves its alias elimination preserves all CFG edge arguments. |
| `ssa.strip-useless` | SSA | no initially | none | Existing `SCfg::strip_useless`; test observability and nested-function references before promotion to default. |
| `ssa.inline-iifes` | SSA | no initially | inline budget | Existing `SCfg::inline_iifes`; narrow but must gain recursion/code-growth and exception/`this`/`arguments` regression coverage before classification as default-safe. |
| `tac.inline-functions` | TAC | no | inline budget | Existing `TFunc::splatted(Mapper)`; expose only after its naming, semantic configuration, recursion, and code-growth contract are reviewed. |
| `ssa.clean-burnt-branches` | SSA | never | none | Existing `clean_func`; it intentionally removes `trim()`/burnt code and requires an explicit external burnt-ID predicate. Exclude it from this CLI until it has a separately designed input contract. |
| `opt-ssa.*` | Opt-SSA | unavailable | n/a | `swc-opt-ssa` currently converts into a speculative representation but has no reverse emitter. Do not expose it as an executable pass. |

Do not label a transformation as fully semantics-preserving merely because it runs with `SemanticCfg::default()`. Audit every operation it invokes, including nested functions and error paths, and promote only after the test gate below passes. The default registry starts conservatively: defaults are limited to audited alias, constant, condition, and load simplifications; all deletion/inlining passes start opt-in.

`Intensity` maps to an explicit per-pass budget (`conservative`, `standard`, `aggressive`), such as maximum fixed-point rounds and maximum inlined nodes. It must be deterministic and finite. Record the effective round/budget values in verbose diagnostics and test that `conservative ≤ standard ≤ aggressive`; never run until no progress without a cap.

## Implementation sequence

### 1. Establish the new package and a non-streaming correctness baseline

1. Add `crates/portal-jsc-optimizer` to workspace members and create `Cargo.toml`, `src/main.rs`, `src/cli.rs`, `src/passes.rs`, `src/pipeline.rs`, and integration-test support. Depend on `swc-cfg`, `swc-tac`, `swc-ssa`, `portal-jsc-swc-util`, SWC parser/codegen/common/visit/transforms-base, `clap`, `anyhow`, and `thiserror`.
2. Parse a full `Module`, apply SWC resolver once with fresh unresolved and top-level marks, then feed the resolved items to the pipeline. This establishes correct binding hygiene first; all binding identity stays as full `Id`.
3. Implement `OptimizationPlan` and `--list-passes`, including stable descriptor order, validation, default selection, intensity resolution, semantic-flag parsing, and helpful failures. Unit-test this without parsing JavaScript.
4. Implement a buffered compatibility adapter: `Module → CfgModule → TModule`, then optimize each `TModule.funcs` function and `TModule.body`. This is deliberately temporary and must be named `BufferedModulePipeline` so it cannot be confused with the streaming implementation.
5. For every function: apply selected pre-SSA TAC passes; convert `TFunc → SFunc`; apply selected SSA passes in descriptor order and bounded rounds; rewrite `SFunc → TFunc` with a deterministic, collision-safe prefix; then apply the selected post-SSA TAC cleanup passes. Nested `Item::Func` bodies must pass through the same plan recursively. Never optimize only top-level functions.
6. Preserve source type parameters, return annotations, async/generator flags, function parameters, import declarations, and every `ExportSpec` through conversion and reconstruction.

### 2. Add a real module re-emitter

Add a `ModuleEmitter` internal module in the CLI package, with an interface equivalent to:

```rust
fn emit_module(
    imports: &[ImportDecl],
    functions: &[EmittedFunction],
    body: TFunc,
    exports: &[ExportSpec],
    options: &EmitOptions,
) -> Result<Module, EmitError>;
```

It hides all reconstitution details from the optimization pipeline. Its required behavior is:

1. Emit imports verbatim and before executable statements.
2. Convert each optimized hoisted `TFunc` with `to_func_with_options`, then `Func → Function`, and emit a function declaration. Use the original function key/name; do not derive identity from a rendered temporary.
3. Reconstruct the top-level optimized `TFunc` as statements without the harness's IIFE wrapper. A dedicated `TFunc → Vec<Stmt>` helper should reuse TAC rewrite logic but must not treat the module body as an ordinary function declaration.
4. Materialize exports from `ExportSpec` after the declarations/body they refer to:
   - `Local` becomes an `ExportNamed` local specifier using the stored hygienic local `Id` and textual export name.
   - `DefaultFunc` becomes `export default <function binding>` or an equivalent declaration form that preserves function binding/evaluation behavior.
   - `DefaultExpr` becomes `export default <local binding>`.
   - `Reexport` and `ReexportAll` reproduce source/module names, spans where required, and `with` attributes.
5. Preserve ordering required by ESM semantics. Introduce an ordered function inventory at the `CfgModuleBuilder`/CLI ingestion seam rather than iterating an existing `HashMap`. Make the inventory key hygienic where it denotes a binding, and textual only for module/export names.
6. Apply output-only hygiene after reconstruction, using a fresh mark that cannot collide with resolved source bindings. Then emit with `swc_ecma_codegen`. This step must not change import/export linkage IDs.

Before using this emitter in the CLI, add module fixtures that cover default/named/aliased exports, anonymous default functions/classes, import aliases, re-exports, `export * as ns`, import attributes, function hoisting, and a binding text collision across distinct syntax contexts.

### 3. Replace the baseline with streaming ingestion

The streaming architecture must not weaken resolver correctness. Implement it in two explicit stages:

1. **Resolver seam.** Add a module-scoped incremental resolver adapter that consumes `ModuleItem`s while maintaining the same binding/hoisting behavior as one whole-module SWC resolver invocation. It must expose resolved items in source order and preserve full `Id`s. If SWC cannot provide this safely through a public incremental interface, add a well-tested repository-owned resolver adapter or retain the buffered resolver; do not resolve items independently.
2. **Optimization seam.** Feed resolved items into `CfgModuleBuilder`. After each `append`, drain `take_functions()`. For each drained function, execute the whole TAC→SSA→TAC pipeline immediately, store only its optimized `TFunc` and ordered metadata, and release the CFG/SSA allocations. At EOF, call `finish()`, optimize its body, and combine the retained functions, imports, exports, and body in `ModuleEmitter`.

Streaming acceptance criteria:

- Parser errors identify the input path and terminate before output replacement.
- A top-level function can be optimized before the next top-level function's IR is constructed.
- Imports, sibling functions, closures, forward references, and top-level declarations resolve identically to whole-module resolution.
- Peak retained IR excludes pre-optimization CFG/SSA for completed functions. Add instrumentation behind a test-only feature if necessary; do not infer this merely from API shape.
- Function declaration order is retained independently of map iteration.

### 4. Harden individual passes and defaults

For each registry entry, document: input invariant, transformation, semantic assumptions, recursive/nested-function behavior, cost model, intensity budget, and postcondition. Place pass-specific tests next to the owning IR crate; place CLI selection and end-to-end tests in `portal-jsc-optimizer`.

Promotion to the default set requires all of:

- a unit test for the transformation's intended positive case;
- a regression test for every known side-effect, exception, closure-capture, `this`, `arguments`, async, generator, and control-flow limitation relevant to the pass;
- differential execution against Node for representative module fixtures;
- no required nonempty `SemanticFlags`;
- re-emission succeeds and output reparses as a module.

Keep `SemanticFlags` visible in diagnostics. Map user spelling to the existing bitflags, reject unknown/duplicate flags, and list each selected pass's required and active assumptions. Defaults must use `SemanticCfg { flags: SemanticFlags::empty(), target: SemanticTarget::ECMAScript }`.

## Validation and test matrix

### Unit tests

- CLI parsing: defaults, replacement selection, exclusions, comma/repeated values, invalid names, invalid intensity, incompatible per-pass override, unsupported syntax, and `--list-passes` without input.
- Registry: stable ordering; default entries are marked full-semantics-preserving; all nondefault entries are excluded without explicit selection; aggressive execution obeys every cap.
- Pipeline: each selected pass observes the intended IR layer; nested `Item::Func` bodies are optimized; no pass runs twice due to duplicate CLI input; fixed-point execution terminates at its cap.
- Emitter: exact AST-level import/export reconstruction for every `ExportSpec` variant and declaration ordering; original hygienic IDs remain distinct when `sym` is equal.

### End-to-end tests

Create fixture pairs under `crates/portal-jsc-optimizer/tests/fixtures/` and run original and optimized modules with Node via a temporary directory. Use a module entry file and supporting imported modules; compare stdout, exit status, and expected thrown-error behavior. Cover:

- imports, live imported bindings, named/default/namespace imports, aliases, and re-exports;
- default expression/function/class exports, named aliases, `export *`, and import attributes where Node supports them;
- closures that mutate captured locals, same-text bindings in nested scopes, top-level hoisting, and cyclic-looking references;
- property getters/setters, proxies, throwing expressions, `eval`, `with` rejection/handling policy, direct and indirect calls, and observable evaluation order;
- `this`, `arguments`, arrow versus ordinary functions, async/await, generators/yield, try/catch/finally, switches, loops, destructuring, spreads, and computed properties;
- every default pass independently and the complete default plan at each intensity;
- every opt-in pass only after it has its own semantic fixture suite.

Run at least:

```bash
cargo fmt --check
cargo test -p portal-jsc-optimizer
cargo test
cargo build --workspace
```

Run `cargo clippy --workspace --all-targets` if the repository's existing warning baseline permits it; otherwise record only new warnings attributable to the CLI. Node-dependent tests must skip only when Node is genuinely absent, not when the optimizer fails.

## Documentation and operational behavior

- Update `README.md` with installation/build invocation, CLI examples, the default-safety guarantee, opt-in/semantic-assumption policy, streaming retention definition, and current ECMAScript-only syntax scope.
- Update `TESTING.md` with the optimizer package commands, module fixture convention, Node comparison strategy, and how to add a pass test.
- `--help` and `--list-passes` are the authoritative machine-adjacent documentation for stable pass names. Keep names lowercase, dotted, and backward-compatible once released.
- Emit concise phase diagnostics to stderr only under `--verbose`; JavaScript output is always clean stdout when `--output -` is used.
- Return distinct, contextual error messages for input I/O, parse errors, unsupported syntax, pass selection/configuration, lowering/rewriting, module emission, code generation, and output replacement. Never leave a partially written destination file.

## Out of scope for the first release

- TypeScript parsing/emission, source maps, minification, bundling, dependency graph traversal, watch mode, disk caching, plugin-loaded passes, JSON configuration files, and a stable IR snapshot format.
- Opt-SSA execution: no SSA/Opt-SSA reverse conversion or JavaScript emitter exists in the workspace.
- Semantics-changing branch pruning via `clean_func`, automatic `SemanticFlags` inference, and unsafe optimization enabled by an "aggressive" shorthand.
- Claiming whole-source streaming while relying on a full-module resolver buffer. The compatibility pipeline is an implementation milestone, not the final streaming feature.

## Delivery milestones

1. **Registry and baseline:** new crate, CLI validation/listing, buffered resolver-backed module roundtrip, atomic output, and no optimization passes enabled yet.
2. **Safe default pipeline:** audited TAC/SSA defaults, recursive function handling, bounded intensity, and Node differential fixtures for all default entries.
3. **Complete module emitter:** imports/exports/type metadata/order roundtrip and module-level end-to-end coverage.
4. **Streaming implementation:** module-scoped resolver seam, incremental parser ingestion, per-function early lowering/optimization, retention tests, and removal of the buffered pipeline from normal execution.
5. **Opt-in maturation:** promote additional passes only through the documented safety gate; keep nonconforming passes explicitly opt-in or unavailable.
