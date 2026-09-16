#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/lean4-prod-text-view.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT

cargo run --manifest-path "$repo_root/rust/Cargo.toml" -p prod-codegen \
  --example text_view_fixture --locked --offline -- "$scratch/fixture" /usr/share/common-licenses/Apache-2.0
node --experimental-vm-modules "$repo_root/rust/prod-codegen/tests/fixtures/text_view_test.mjs" \
  "$scratch/fixture/invoke"

for entry in invoke invalid oversized; do
  adapter="$scratch/fixture/$entry/adapter"
  patch="patch.crates-io.text-view-core.path='$scratch/fixture/core'"
  cargo generate-lockfile --manifest-path "$adapter/Cargo.toml" --offline --config "$patch"
  CARGO_TARGET_DIR="$scratch/cargo-target" cargo build --manifest-path "$adapter/Cargo.toml" \
    --target wasm32-unknown-unknown --release --locked --offline --config "$patch"
  wasm="$scratch/cargo-target/wasm32-unknown-unknown/release/text_view_$entry.wasm"
  "$CARGO_HOME/bin/wasm-tools" validate "$wasm"
  "$CARGO_HOME/bin/wasm-bindgen" --target nodejs --out-dir "$scratch/$entry" --out-name adapter "$wasm"
  "$CARGO_HOME/bin/wasm-bindgen" --target web --out-dir "$scratch/fixture/$entry/browser" --out-name text_view_core "$wasm"
done
node "$repo_root/rust/prod-codegen/tests/fixtures/text_view_wasm_test.cjs" "$scratch"
node "$repo_root/rust/prod-codegen/tests/fixtures/text_view_browser_test.mjs" "$scratch/fixture"
echo "Text View: deterministic closure, DOM transports, UTF-8 limits, and actual Wasm probes passed"
