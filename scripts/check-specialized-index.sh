#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/lean4-prod-index.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
node "$repo_root/scripts/check-index-provenance.mjs"
cd "$repo_root/lean"
lake build IndexFixture ProdLib
lake env lean Conformance/ByteIndex.lean
lake env lean Conformance/ByteSlice.lean
for output in first second; do
  lake exe prod-export --module IndexFixture.Main \
    --root IndexFixture.Main.entry --root IndexFixture.Main.read \
    --root IndexFixture.Main.readSlice --root IndexFixture.Main.sliceEntry \
    --ir-module ByteIndex --out "$scratch/$output-export"
done
for artifact in kernel.ir roots.json coverage.json; do
  cmp "$scratch/first-export/$artifact" "$scratch/second-export/$artifact"
done
rg -Fq '(index ' "$scratch/first-export/kernel.ir"
rg -Fq '(slice ' "$scratch/first-export/kernel.ir"

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
cp "$repo_root/rust/prod-codegen/tests/fixtures/byte_slice_generated_test.rs" "$scratch/first/tests/slice.rs"
cd "$scratch/first"
RUSTC_WRAPPER= cargo test --locked --offline
RUSTC_WRAPPER= cargo test --locked --offline --no-default-features

for entry in entry sliceEntry; do
output_cap=1
if [ "$entry" = sliceEntry ]; then output_cap=2; fi
for output in "first-$entry" "second-$entry"; do
  cd "$repo_root/rust"
  RUSTC_WRAPPER= cargo run --locked --offline -p prod-cli -- core-wasm \
    "$scratch/first-export/kernel.ir" --output "$scratch/$output" \
    --entry "$entry" --export-name holo_run --input-allocation-cap 64 \
    --output-allocation-cap "$output_cap" --maximum-pages 4 --crate-name byte-index-guest
  cd "$scratch/$output"
  for profile in debug release; do
    flags=()
    if [ "$profile" = release ]; then flags+=(--release); fi
    # Keep debug information while removing the temporary build-directory identity.
    # cargo rustc appends this flag without replacing the bounded Wasm linker flags.
    CARGO_PROFILE_DEV_DEBUG=2 RUSTC_WRAPPER= cargo rustc --locked --offline "${flags[@]}" -- \
      --remap-path-prefix "$PWD=."
    node "$repo_root/rust/prod-codegen/tests/fixtures/byte_index_wasm_test.mjs" \
      "$scratch/$output/target/wasm32-unknown-unknown/$profile/byte_index_guest.wasm" "$entry"
  done
done
for profile in debug release; do
  cmp "$scratch/first-$entry/target/wasm32-unknown-unknown/$profile/byte_index_guest.wasm" \
    "$scratch/second-$entry/target/wasm32-unknown-unknown/$profile/byte_index_guest.wasm"
done
cmp "$scratch/first-$entry/generation-manifest.json" "$scratch/second-$entry/generation-manifest.json"
done
echo 'Imported byte-index/slice provenance, rejection, deterministic native and bounded Wasm execution passed'
