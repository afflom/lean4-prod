#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/lean4-prod-index.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
node "$repo_root/scripts/check-index-provenance.mjs"
cd "$repo_root/lean"
lake build IndexFixture ProdLib
lake env lean Conformance/ByteIndex.lean
for output in first second; do
  lake exe prod-export --module IndexFixture.Main \
    --root IndexFixture.Main.entry --root IndexFixture.Main.read \
    --ir-module ByteIndex --out "$scratch/$output-export"
done
for artifact in kernel.ir roots.json coverage.json; do
  cmp "$scratch/first-export/$artifact" "$scratch/second-export/$artifact"
done
rg -Fq '(index ' "$scratch/first-export/kernel.ir"

for output in first second; do
  cd "$repo_root/rust"
  RUSTC_WRAPPER= cargo run --locked --offline -p prod-cli -- cargo \
    "$scratch/first-export/kernel.ir" --output "$scratch/$output" \
    --name byte-index-fixture --version 0.1.0 \
    --description 'LexLean imported byte-index compiler fixture' \
    --repository https://github.com/auser/lean4-prod \
    --homepage https://github.com/auser/lean4-prod \
    --readme "$repo_root/fixtures/lexlean-index/README.md" \
    --license-mit "$repo_root/rust/prod-codegen/tests/fixtures/LICENSE-MIT" \
    --license-apache /usr/share/common-licenses/Apache-2.0
done
diff -ru "$scratch/first" "$scratch/second"
mkdir "$scratch/first/tests"
cp "$repo_root/rust/prod-codegen/tests/fixtures/byte_index_generated_test.rs" "$scratch/first/tests/index.rs"
cd "$scratch/first"
RUSTC_WRAPPER= cargo test --locked --offline
RUSTC_WRAPPER= cargo test --locked --offline --no-default-features

for output in first-guest second-guest; do
  cd "$repo_root/rust"
  RUSTC_WRAPPER= cargo run --locked --offline -p prod-cli -- core-wasm \
    "$scratch/first-export/kernel.ir" --output "$scratch/$output" \
    --entry entry --export-name holo_run --input-allocation-cap 64 \
    --output-allocation-cap 1 --maximum-pages 4 --crate-name byte-index-guest
  cd "$scratch/$output"
  for profile in debug release; do
    flags=()
    if [ "$profile" = release ]; then flags+=(--release); fi
    RUSTC_WRAPPER= cargo build --locked --offline "${flags[@]}"
    node "$repo_root/rust/prod-codegen/tests/fixtures/byte_index_wasm_test.mjs" \
      "$scratch/$output/target/wasm32-unknown-unknown/$profile/byte_index_guest.wasm"
  done
done
for profile in debug release; do
  cmp "$scratch/first-guest/target/wasm32-unknown-unknown/$profile/byte_index_guest.wasm" \
    "$scratch/second-guest/target/wasm32-unknown-unknown/$profile/byte_index_guest.wasm"
done
cmp "$scratch/first-guest/generation-manifest.json" "$scratch/second-guest/generation-manifest.json"
echo 'Imported byte-index provenance, rejection, deterministic native and bounded Wasm execution passed'
