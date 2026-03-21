# jsaw-core

[![License: MPL-2.0](https://img.shields.io/badge/License-MPL--2.0-blue.svg)](https://opensource.org/licenses/MPL-2.0)
[![Version](https://img.shields.io/badge/version-0.8.0--pre.11-orange.svg)](https://github.com/portal-co/jsaw-core)

**jsaw-core** is a Rust library providing a multi-stage intermediate representation (IR) pipeline for ECMAScript (JavaScript). It converts JavaScript/TypeScript source code, parsed via [SWC](https://swc.rs/), through successive IR lowerings: CFG → TAC → SSA → optimized SSA.

This is part of the Portal Compiler Organization. The workspace is pre-release and under active development; APIs change between pre-release versions.

## What it does

The project provides a series of IRs intended for use as a compiler backend for JavaScript. Each stage lowers the representation closer to a form suitable for analysis or code generation:

1. **Parse**: SWC parses JavaScript or TypeScript source into an AST.
2. **CFG** (`swc-cfg`): The AST is converted to a control flow graph. Blocks contain raw SWC `Stmt` nodes; terminators handle returns, jumps, conditional branches, switches, and exception handlers (`try/catch`). The CFG can also be relooped back to JavaScript using the `relooper` crate.
3. **TAC** (`swc-tac`): The CFG is lowered to three-address code where each statement performs one operation. Expressions are broken into explicit assignments. Lambdas and atoms are resolved; constant propagation is available at this stage.
4. **SSA** (`swc-ssa`): TAC is transformed into static single assignment form. This implementation uses block parameters rather than phi-functions: basic blocks take typed parameters and predecessors pass arguments when jumping. Values (`SValue`) are stored in a separate arena from blocks.
5. **Optimized SSA** (`swc-opt-ssa`): An extended SSA form that adds type information (`OptType`) to values, type assertion nodes, and deoptimization points for speculative optimizations.

There is no code generation backend in this repository. This repo provides the IR library only.

## Crate structure

All crates are published under the `portal-jsc-*` package name prefix. Short aliases are used in the workspace dependency table.

| Crate directory | Package name | Purpose |
|---|---|---|
| `crates/swc-cfg` | `portal-jsc-swc-cfg` | CFG representation and AST→CFG conversion |
| `crates/swc-tac` | `portal-jsc-swc-tac` | Three-address code IR; CFG→TAC conversion |
| `crates/swc-ssa` | `portal-jsc-swc-ssa` | SSA form; TAC→SSA conversion |
| `crates/swc-opt-ssa` | `portal-jsc-swc-opt-ssa` | Optimized SSA with type info; SSA→OptSSA conversion |
| `crates/swc-ll-common` | `portal-jsc-swc-ll-common` | Shared types (Item, TCallee, etc.) used by TAC and SSA; `define_arena!` macro |
| `crates/swc-util` | `portal-jsc-swc-util` | SWC AST utilities, semantic configuration, native function resolution |
| `crates/portal-jsc-common` | `portal-jsc-common` | Common types: primordials, semantic flags, inline assembly constructs |
| `crates/simpl-js` | `portal-jsc-simpl-js` | Legacy AST for the "Simpl" simplified JS dialect (optional, mostly inactive) |
| `crates/portal-jsc-generator` | `portal-jsc-generator` | Binary that generates `packages/jsaw-intrinsics-base/index.ts` |

### Key types by crate

**swc-cfg**
- `Func`: a function as a CFG, with SWC `Param` nodes, async/generator flags, and optional TypeScript type annotations
- `Cfg`: arena of `Block` values
- `Block`: list of `Stmt` + an `End` (terminator + exception handler)
- `Term`: `Return`, `Throw`, `Jmp`, `CondJmp`, `Switch`, `Default`
- `Catch`: either propagate (`Throw`) or jump to a handler block with a binding pattern
- `BlockArena` / `BlockId`: specialized arena and index types (see arena infrastructure below)

**swc-tac**
- `TFunc`, `TCfg`, `TBlock`, `TStmt`, `TTerm`
- `Item`: the right-hand side of a TAC assignment (literal, binary op, call, member read, object/array construction, spread, etc.)
- `LId`: left-hand side (plain identifier, member assignment, or private field)
- `TBlockArena` / `TBlockId`

**swc-ssa**
- `SFunc`, `SCfg`, `SBlock`, `SValueW`, `STerm`, `STarget`, `SCatch`
- `SValue`: SSA value variants including parameters, operations (via `Item`), loads, stores, function references, and calls
- `SBlockArena` / `SBlockId`, `SValueArena` / `SValueId`
- Block parameters replace phi-functions: jump targets (`STarget`) carry argument lists

**swc-opt-ssa**
- `OptValue<I, B, F, D>`: wraps `SValue` and adds `Assert` (type guard) and `Deopt` (deoptimization point) variants
- `OptType`: type information attached to values
- `OptBlockArena` / `OptBlockId`, `OptValueArena` / `OptValueId`

**portal-jsc-common**
- `Primordial`: enum of recognized JS built-ins (`globalThis`, `Object`, `Reflect.get`, `Math.imul`, etc.) used for optimization
- `SemanticFlags`: bitfield of compiler assumptions (no monkey-patching, no JIT, frozen objects, native function recognition, etc.)
- `SemanticTarget`: target engine variants — `ECMAScript` (default), `Simpl`, `MuJSC`, `Porffor`
- `Asm<I>`: inline assembly constructs (currently just `OrZero`, the `x | 0` integer conversion idiom)

### Arena infrastructure

All IR arenas previously used `id-arena`. This dependency has been removed and replaced with a `define_arena!` macro in `swc-ll-common` that generates paired specialized arena and ID types (e.g., `BlockArena` + `BlockId`). Each ID type is `#[repr(transparent)]` over `usize`, fully `rkyv`-serializable, and incompatible with IDs from other arenas at the type level. This migration is complete across all five crates.

### JavaScript package

A small npm workspace lives alongside the Rust crates:

- `packages/jsaw-intrinsics-base/`: TypeScript file generated by `portal-jsc-generator`. Exports `fast_add`, `fast_mul`, `fast_imul`, and similar arithmetic intrinsics, plus `assert_*`, `comptime_*`, `inlineme`, and `trim` — all backed by `globalThis['~Natives_*']` hooks if present, with no-op fallbacks otherwise.

## Compilation targets

The `SemanticTarget` enum lists intended targets:
- **ECMAScript**: standard output (default)
- **Simpl**: the simplified dialect with its own AST (`simpl-js` crate); the `simpl-legacy` feature in `swc-tac` enables a legacy conversion path
- **MuJSC** and **Porffor**: engine-specific targets (no versions defined yet; both enums are empty and `#[non_exhaustive]`)

No code generation backends exist in this repository.

## Building

Requires Rust with edition 2024 (stable toolchain that supports it).

```bash
# Build all crates
cargo build

# Build in release mode
cargo build --release

# Run tests
cargo test

# Generate the intrinsics TypeScript file
cargo run --bin portal-jsc-generator -- <path-to-repo-root>
```

The `rkyv-impl` feature enables `rkyv` serialization/deserialization on all IR types. It must be enabled consistently across crates (enabling it on one crate also requires enabling it on its dependencies via their feature flags).

## Testing

The `tests/` and `harness/` directories are currently empty. The `TESTING.md` file describes the intended structure (Vitest for JS, `cargo test` for Rust) but notes that specific test cases are a TODO.

## Current status

- Version: `0.8.0-pre.11`
- The arena infrastructure migration (replacing `id-arena` with custom `define_arena!`-generated types) is complete across all crates.
- Around 380 compiler warnings exist unrelated to the migration.
- There are no tests in `tests/` yet.
- The `simpl-js` crate and the `simpl-legacy` feature in `swc-tac` are mostly inactive; the Simpl path is marked as a legacy code path in comments and documentation.
- The `swc-opt-ssa` stage is optional in a pipeline; it can increase code size for JS output targets, according to in-code documentation.
- MuJSC and Porffor targets are declared in `SemanticTarget` but not implemented (empty enums).

## External dependencies of note

- [SWC](https://swc.rs/) (`swc_ecma_ast`, `swc_ecma_visit`, etc.): parser and AST types
- [`codegen-utils`](https://github.com/portal-co/codegen-utils) (git dependency, `master` and `dev/0.3` branches): `cfg-traits`, `ssa-traits`, `ssa-impls`, `ssa-reloop` — generic CFG and SSA trait definitions and utilities
- [`relooper`](https://crates.io/crates/relooper): converts a CFG back into structured control flow (loops, switches) for JS output
- [`rkyv`](https://crates.io/crates/rkyv): zero-copy serialization for IR types (behind `rkyv-impl` feature)
- [`portal-solutions-swibb`](https://github.com/portal-co/swibb) (git dependency): constant collection utilities
- `portal-pc-asm-common`: assembly common types (used in `portal-jsc-common`)

## License

Mozilla Public License 2.0 (MPL-2.0). See `LICENSE.md`.
