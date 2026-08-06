# Default
default:
    @just --list

# Full pipeline: export from Lean, then verify the Rust build against it.
prod: prod-export test roots-check

# Export prod from lean
prod-export:
    cd lean && lake exe prod-export

# Build rust debug
build:
    cd rust && cargo build

# Build rust production
build-prod:
    cd rust && cargo build --release

# Test rust workspace
test:
    cd rust && cargo test --workspace

# Validate the generated theorem dependency graph.
roots-check:
    cd rust && cargo run -p prod-cli -- roots check ../roots.json

# Link rust code
lint:
    cd rust && cargo clippy --all-targets -- -D warnings

# Portable half must stay no_std/wasm32-clean.
wasm-check:
    cd rust && RUSTC=$(rustup which --toolchain stable rustc) rustup run stable cargo build -p prod-ir -p prod-codegen -p prod-wasm --target wasm32-unknown-unknown
