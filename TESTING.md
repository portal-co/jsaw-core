# Testing Guide

## Overview

This repo has two test suites:

- **Rust unit tests** — `cargo test` (runs tests inside crates)
- **Roundtrip integration tests** — compile a JS fixture through the IR pipeline, run both the original and the compiled output with `node`, and assert identical stdout

## Quick start

```bash
# Unit tests only
cargo test

# Build the harness binary (required before running integration tests)
cargo build --bin swc-test-harness

# Run roundtrip integration tests
cargo test -p portal-jsc-swc-test-harness
```

## Roundtrip harness

The harness (`crates/swc-test-harness/`) is a binary that:

1. Reads a plain JS script (no `import`/`export`)
2. Parses it with SWC
3. Converts: AST → `CfgModule` → `TModule` (TAC) → back to CFG → back to SWC AST
4. Emits the reconstructed JavaScript to stdout

The integration tests in `crates/swc-test-harness/tests/roundtrip.rs`:
- Run the original fixture with `node` → capture stdout
- Run the harness on the fixture → get compiled JS
- Run the compiled JS with `node` → capture stdout
- Assert the two outputs are identical

## Test fixtures

JS fixture files live in `tests/fixtures/`. Each must be a self-contained script
(no `import`/`export`, deterministic stdout):

| File | Tests |
|------|-------|
| `arith.js` | Basic arithmetic operators |
| `fib.js` | Recursive functions |
| `closure.js` | Variable capture / mutation |
| `loop.js` | `for` loop with accumulator |
| `cond.js` | `if`/`else` and ternary |

## Adding a new fixture

1. Create `tests/fixtures/my_feature.js` — a self-contained script that prints
   deterministic output via `console.log`.
2. Add a test function in `crates/swc-test-harness/tests/roundtrip.rs`:
   ```rust
   #[test]
   fn my_feature() { roundtrip("my_feature.js"); }
   ```
3. Run `cargo test -p portal-jsc-swc-test-harness -- my_feature` to verify.

## Requirements

- Rust toolchain (edition 2024)
- Node.js (`node` on PATH) for integration tests

## Harness internals

```
harness binary (src/main.rs)
  swc_ecma_parser::parse_file_as_script
        ↓
  CfgModule::try_from(module)          [crates/swc-cfg]
        ↓
  TModule::try_from(cfg_module)        [crates/swc-tac]
        ↓
  Options::bud → TFunc::to_func_with_options  [crates/swc-tac/src/rew.rs]
        ↓
  Function::from(cfg_func)             [crates/swc-cfg/src/lib.rs:126]
        ↓
  swc_ecma_codegen::Emitter::emit_script
        ↓ stdout
```
