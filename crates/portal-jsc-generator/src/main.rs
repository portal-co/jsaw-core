//! Portal JSC code generator.
//!
//! This binary is the main code generation tool for the Portal JavaScript Compiler.
//! It generates TypeScript/JavaScript intrinsics and runtime support files.
//!
//! # Usage
//!
//! ```bash
//! portal-jsc-generator <source-root>
//! ```
//!
//! Where `<source-root>` is the root directory of the project. The generator
//! will create necessary intrinsic files in the `packages/` directory.
//!
//! # Generated Files
//!
//! - `packages/jsaw-intrinsics-base/index.ts`: Base intrinsic functions for
//!   fast operations and type assertions

use itertools::Itertools;

/// Main entry point for the generator.
///
/// Takes the source root directory as an argument and generates intrinsic files.
fn main() {
    let mut args = std::env::args();
    args.next();
    let root = args.next().expect("the source root");
    emit_base_intrinsics(&root);
}
/// Emits the base intrinsics TypeScript file.
///
/// Generates TypeScript declarations for native/intrinsic functions that can be
/// recognized and optimized by the compiler. These include fast arithmetic
/// operations and type assertions.
///
/// # Arguments
///
/// * `source_root` - The source root directory path
fn emit_base_intrinsics(source_root: &str) {
    std::fs::write(
        format!("{source_root}/packages/jsaw-intrinsics-base/index.ts"),
        format!(
            "
{}
    ",
            [
                ("a + b", "fast_add","number"),
                ("a & b", "fast_and","number"),
                ("a | b", "fast_or","number"),
                ("a === b", "fast_eq","boolean"),
                ("a - b", "fast_sub","number"),
                ("a << b", "fast_shl","number"),
                ("a * b", "fast_mul","number"),
                ("Math.imul(a,b)", "fast_imul","number"),
            ]
            .into_iter()
            .map(|(a, b,c)| format!("export const {b}: (a: number,b: number) => {c} = (globalThis as any)['~Natives_{b}'] ?? ((a: any, b: any) => {a});"))
            .chain(["assert", "comptime"].into_iter().flat_map(|a| [
                format!("export const {a}_string: (a: string) => string =  (globalThis as any)['~Natives_{a}_string'] ?? ((a: string) => a)"),
                format!("export const {a}_number: (a: number) => number = (globalThis as any)['~Natives_{a}_number'] ??( (a: number) => a)"),
                format!("export const {a}_static_fn: (a: Function) => Function = (globalThis as any)['~Natives_{a}_static_fn'] ?? ((a: Function) => a)"),
            ])).chain([
                format!("export const inlineme: () => void = (globalThis as any)['~Natives_inlineme'] ?? (()=>{{}})"),
                format!("export const inlineme_n: (n: number) => void = (globalThis as any)['~Natives_inlineme_n'] ?? ((n: number)=>{{}})")
            ])
            .join("\n")
        ),
    )
    .expect("to write the intrinsics")
}
