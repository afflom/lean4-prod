# Default
default:
    @just --list

# Full pipeline: export from Lean, then verify the Rust build against it.
prod: prod-export conformance test test-assertions no-alloc roots-check subset-check

# Export prod from lean
prod-export:
    cd lean && lake exe prod-export

# The conformance golden pins Lean-side lowering. `prod-export` rewrites it; this
# fails if the rewrite changed anything, so lowering changes surface as a diff.
#
# `git diff HEAD`, not `git diff`: the latter compares the worktree against the
# INDEX, so any `git add -A` before this recipe made it pass unconditionally --
# a gate you can switch off by staging. `HEAD` compares against the commit,
# which is what "the committed golden matches the generator" actually means.
conformance:
    cd lean && lake exe prod-export
    git diff HEAD --exit-code lean/Conformance/golden.ir lean/Conformance/golden-rejected.ir

# Accept the current lowering as the new golden. Review the diff before running.
# Staging is no longer enough to satisfy `conformance` above (that was the bug):
# commit the blessed golden, then the gate passes.
conformance-bless:
    cd lean && lake exe prod-export
    git add lean/Conformance/golden.ir lean/Conformance/golden-rejected.ir

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

# `git diff HEAD`, not `git diff` — same reason as `conformance` above: staging
# the regenerated contract must not be what makes its own gate pass.
subset-check: subset
    git diff HEAD --exit-code specs/lean-for-production.md

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
