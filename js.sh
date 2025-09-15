cd $(dirname $0)
cargo run -p portal-jsc-generator -- $(pwd)
cd packages/jsaw-intrinsics-base
npx zshy -p ../../tsconfig.json