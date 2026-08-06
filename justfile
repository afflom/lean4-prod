# Full pipeline: export from Lean, then verify the Rust build against it.
prod: export test

export:
    cd lean && lake exe prod-export

build:
    cd rust && cargo build

test:
    cd rust && cargo test

lint:
    cd rust && cargo clippy --all-targets -- -D warnings

# Portable half must stay no_std/wasm32-clean.
wasm-check:
    cd rust && cargo build -p prod-ir -p prod-codegen --target wasm32-unknown-unknown
