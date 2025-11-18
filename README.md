# jsaw-core

[![License: MPL-2.0](https://img.shields.io/badge/License-MPL--2.0-blue.svg)](https://opensource.org/licenses/MPL-2.0)
[![Version](https://img.shields.io/badge/version-0.8.0--pre.9-orange.svg)](https://github.com/portal-co/jsaw-core)

**jsaw-core** is a compiler framework for ECMAScript (JavaScript) that provides multiple intermediate representations (IR) for optimization and code generation. It transforms JavaScript/ECMAScript code through several lowering stages, from high-level syntax to optimized intermediate forms suitable for various compilation targets.

## Overview

jsaw-core provides a multi-stage compilation pipeline for JavaScript:

1. **Source Parsing**: Using SWC (Speedy Web Compiler) to parse JavaScript/TypeScript
2. **Control Flow Graph (CFG)**: Converts parsed AST into control flow graphs
3. **Three-Address Code (TAC)**: Lowers CFG to three-address code representation
4. **Static Single Assignment (SSA)**: Transforms TAC into SSA form for optimization
5. **Optimizations**: Performs various optimizations on SSA form
6. **Code Generation**: Targets various backends (WebAssembly, native code, etc.)

## Architecture

The project is organized as a Cargo workspace with several crates, each handling a specific compilation stage:

### Core Crates

- **`portal-jsc-common`**: Common types and utilities used across all stages
  - Native function definitions
  - Semantic configuration
  - Syntax helpers

- **`swc-cfg`**: Control Flow Graph representation
  - Converts JavaScript AST to CFG
  - Basic block structure
  - Control flow analysis

- **`swc-tac`**: Three-Address Code intermediate representation
  - Converts CFG to TAC
  - Single-assignment form (not SSA yet)
  - Statement-based IR with explicit control flow

- **`swc-ssa`**: Static Single Assignment form
  - Converts TAC to SSA
  - Φ-functions for merging values
  - Block parameters for SSA invariants

- **`swc-opt-ssa`**: SSA-level optimizations
  - Constant propagation
  - Dead code elimination
  - Other optimization passes

### Utility Crates

- **`swc-util`**: Shared utilities for SWC-based transformations
  - Type utilities
  - Import mapping
  - Semantic analysis helpers

- **`swc-ll-common`**: Low-level common utilities
  - Shared types for lower-level IRs
  - Fetching and resolution helpers

- **`simpl-js`**: Legacy Simpl dialect AST package
  - Legacy AST implementation for the "Simpl" JavaScript subset
  - Provides dialect-specific AST types and transformations

### Applications

- **`portal-jsc-generator`**: Native bindings generator
  - Generates TypeScript/JavaScript bindings for native functions
  - Creates intrinsics based on definitions in `portal-jsc-common/src/natives.rs`
  - Does not depend on or use most of the compilation pipeline

## Building

```bash
# Build all crates
cargo build

# Build in release mode
cargo build --release

# Run tests
cargo test
```

## Usage

The typical compilation flow:

1. Parse JavaScript source using SWC
2. Convert to CFG using `swc-cfg`
3. Lower to TAC using `swc-tac`
4. Transform to SSA using `swc-ssa`
5. Optimize using `swc-opt-ssa` (optional - can be skipped for different optimization strategies)
6. Generate target code

**Note on `swc-opt-ssa`**: This stage can be skipped if different optimizations are needed. Most generic optimizations are already implemented in `swc-tac` and `swc-ssa`. Pipelines targeting JavaScript output may benefit from skipping `swc-opt-ssa` as it can currently increase code size.

Example using the generator:

```bash
cargo run --bin portal-jsc-generator -- [options] <input.js>
```

## Intermediate Representations

### TAC (Three-Address Code)

TAC represents computations as a sequence of simple statements, each with at most one operator:

- **TFunc**: Function representation with entry block and parameters
- **TCfg**: Control flow graph with basic blocks
- **TBlock**: Basic block containing statements
- **TStmt**: Individual statement (assignment, call, etc.)
- **TTerm**: Block terminator (return, jump, conditional, etc.)

### SSA (Static Single Assignment)

SSA form ensures each variable is assigned exactly once:

- **SFunc**: Function in SSA form
- **SCfg**: SSA control flow graph
- **SBlock**: SSA basic block with block parameters
- **SValue**: SSA values (parameters, operations, loads, stores)
- **STerm**: SSA block terminators with target blocks and arguments

## Key Features

- **Multiple IR Levels**: Gradual lowering from high-level to low-level representations
- **Type Preservation**: Optional TypeScript type annotations preserved through pipeline (work-in-progress)
- **Optimization Infrastructure**: Framework for implementing analyses and transformations
- **Extensible**: Designed to support multiple compilation targets
- **No Unsafe**: Safe Rust throughout (as per project requirements)

## License

This project is licensed under the Mozilla Public License 2.0 (MPL-2.0). See the workspace Cargo.toml for details.

## Contributing

This is part of the Portal Compiler Organization projects. Contributions should maintain:

- Safe Rust (no `unsafe` blocks)
- Minimal API changes
- Comprehensive documentation
- Clear commit history

## Related Projects

- [SWC (Speedy Web Compiler)](https://swc.rs/): The underlying JavaScript/TypeScript parser
- [codegen-utils](https://github.com/portal-co/codegen-utils): Shared utilities for SSA and CFG traits

## Status

Version 0.8.0-pre.9 - Pre-release development version. APIs may change between pre-release versions.
