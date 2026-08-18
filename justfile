# Default
default:
    @just --list

# Full pipeline: export from Lean, then verify the Rust build against it.
prod: lean-fixtures prod-export conformance test test-assertions no-alloc roots-check subset-check

# Compile the standalone Lean proof-fixture library. These declarations are
# real kernel-checked proofs, but are not part of the production export target.
lean-fixtures:
    cd lean && lake build ProofFixtures

# Export prod from lean
prod-export:
    cd lean && lake exe prod-export

# The conformance golden pins Lean-side lowering. `prod-export` rewrites it; this
# fails if the rewrite changed anything, so lowering changes surface as a diff.
conformance:
    cd lean && lake exe prod-export
    git diff --exit-code lean/Conformance/golden.ir

# Accept the current lowering as the new golden. Review the diff before running.
conformance-bless:
    cd lean && lake exe prod-export
    git add lean/Conformance/golden.ir

# Build rust debug
build:
    cd rust && cargo build

# Build rust production
build-prod:
    cd rust && cargo build --release

# Test rust workspace
test:
    cd rust && cargo test --workspace

# Same tests, optimized, with debug/overflow assertions left on. A release
# build that silently wraps where the debug build panics is a bug we want to
# hear about before shipping.
test-assertions:
    cd rust && cargo test --workspace --profile release-assertions

# Certify that the generated code performs zero heap activity. Serial: the
# counting allocator is process-global.
no-alloc:
    cd rust && cargo test -p prod-core --test no_alloc -- --test-threads=1

# Validate the generated theorem dependency graph.
roots-check:
    cd rust && cargo run -p prod-cli -- roots check ../roots.json

# The published subset contract is generated from the implementation, so it
# cannot describe a fragment the code does not implement.
subset:
    cd rust && cargo run -p prod-cli -- subset ../subset.json --output ../specs/lean-for-production.md

subset-check: subset
    git diff --exit-code specs/lean-for-production.md

# Link rust code
lint:
    cd rust && cargo clippy --all-targets -- -D warnings

# Formatting is gated, not merely done once — otherwise it drifts immediately.
fmt-check:
    cd rust && cargo fmt --all -- --check

# Apply formatting.
fmt:
    cd rust && cargo fmt --all

# Portable half must stay no_std/wasm32-clean.
wasm-check:
    cd rust && RUSTC=$(rustup which --toolchain stable rustc) rustup run stable cargo build -p prod-ir -p prod-codegen -p prod-wasm --target wasm32-unknown-unknown
