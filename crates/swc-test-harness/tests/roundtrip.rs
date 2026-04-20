//! Roundtrip tests: compile each fixture through the jsaw-core pipeline and
//! verify that running the result with `node` produces identical stdout.

use std::io::Write as _;
use std::process::Command;

fn harness_bin() -> std::path::PathBuf {
    // Locate the binary relative to the test executable in target/debug/deps/.
    let mut p = std::env::current_exe().expect("current_exe");
    // Go up: deps → debug → target
    p.pop();
    p.pop();
    p.push("swc-test-harness");
    p
}

fn fixtures_dir() -> std::path::PathBuf {
    // CARGO_MANIFEST_DIR is the harness crate; fixtures live two levels up.
    let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.join("../../tests/fixtures")
}

fn roundtrip(fixture: &str) {
    let fixture_path = fixtures_dir().join(fixture);
    let fixture_str = fixture_path.to_str().unwrap();

    // Run the original fixture with node.
    let orig = Command::new("node")
        .arg(fixture_str)
        .output()
        .expect("node not found — install Node.js");
    assert!(
        orig.status.success(),
        "node failed on original {fixture}:\n{}",
        String::from_utf8_lossy(&orig.stderr)
    );

    // Compile fixture through the harness.
    let compiled = Command::new(harness_bin())
        .arg(fixture_str)
        .output()
        .expect("harness binary not found — run `cargo build --bin swc-test-harness` first");
    assert!(
        compiled.status.success(),
        "harness failed on {fixture}:\n{}",
        String::from_utf8_lossy(&compiled.stderr)
    );

    // Write compiled JS to a temp file and run with node.
    let mut tmp = tempfile::NamedTempFile::new().unwrap();
    tmp.write_all(&compiled.stdout).unwrap();

    let compiled_out = Command::new("node")
        .arg(tmp.path())
        .output()
        .expect("node not found");
    assert!(
        compiled_out.status.success(),
        "node failed on compiled {fixture}:\n{}\n--- compiled JS ---\n{}",
        String::from_utf8_lossy(&compiled_out.stderr),
        String::from_utf8_lossy(&compiled.stdout),
    );

    assert_eq!(
        String::from_utf8_lossy(&orig.stdout),
        String::from_utf8_lossy(&compiled_out.stdout),
        "roundtrip output mismatch for {fixture}\n--- compiled JS ---\n{}",
        String::from_utf8_lossy(&compiled.stdout),
    );
}

#[test]
fn arith() {
    roundtrip("arith.js");
}

#[test]
fn fib() {
    roundtrip("fib.js");
}

#[test]
fn closure() {
    roundtrip("closure.js");
}

#[test]
fn loop_sum() {
    roundtrip("loop.js");
}

#[test]
fn cond() {
    roundtrip("cond.js");
}
