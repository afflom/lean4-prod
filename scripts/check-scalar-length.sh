#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/lean4-prod-scalar-length.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
node "$repo_root/scripts/check-scalar-length-provenance.mjs"
cd "$repo_root/lean"
lake build Conformance.LexLeanScalarLength ProdLib
lake env lean Conformance/ScalarLength.lean
for output in first second; do
  lake exe prod-export --module Conformance.LexLeanScalarLength \
    --root ScalarLengthFixture.Main.byteLength --root ScalarLengthFixture.Main.entry \
    --root ScalarLengthFixture.Main.nestedLength --root ScalarLengthFixture.Main.scalarLength \
    --ir-module ScalarLength --out "$scratch/$output-export"
done
for artifact in kernel.ir roots.json coverage.json; do
  cmp "$scratch/first-export/$artifact" "$scratch/second-export/$artifact"
done
rg -Fq '(string-length ' "$scratch/first-export/kernel.ir"
rg -Fq '(length ' "$scratch/first-export/kernel.ir"

for output in first second; do
  cd "$repo_root/rust"
  RUSTC_WRAPPER= cargo run --locked --offline -p prod-cli -- cargo \
    "$scratch/first-export/kernel.ir" --output "$scratch/$output" \
    --name scalar-length-fixture --version 0.1.0 \
    --description 'LexLean Unicode scalar-length compiler fixture' \
    --repository https://github.com/auser/lean4-prod \
    --homepage https://github.com/auser/lean4-prod \
    --readme "$repo_root/fixtures/lexlean-scalar-length/README.md" \
    --license-mit "$repo_root/rust/prod-codegen/tests/fixtures/LICENSE-MIT" \
    --license-apache /usr/share/common-licenses/Apache-2.0
done
diff -ru "$scratch/first" "$scratch/second"
mkdir "$scratch/first/tests"
cp "$repo_root/rust/prod-codegen/tests/fixtures/scalar_length_generated_test.rs" "$scratch/first/tests/length.rs"
cd "$scratch/first"
for profile in debug release; do
  flags=()
  if [ "$profile" = release ]; then flags+=(--release); fi
  RUSTC_WRAPPER= cargo test --locked --offline "${flags[@]}"
  RUSTC_WRAPPER= cargo test --locked --offline --no-default-features "${flags[@]}"
done

for output in first-guest second-guest; do
  cd "$repo_root/rust"
  RUSTC_WRAPPER= cargo run --locked --offline -p prod-cli -- core-wasm \
    "$scratch/first-export/kernel.ir" --output "$scratch/$output" \
    --entry entry --export-name holo_run --input-allocation-cap 256 \
    --output-allocation-cap 1 --maximum-pages 4 --crate-name scalar-length-guest
  cd "$scratch/$output"
  for profile in debug release; do
    flags=()
    if [ "$profile" = release ]; then flags+=(--release); fi
    # Keep debug information while removing the temporary build-directory identity.
    # cargo rustc appends this flag without replacing the bounded Wasm linker flags.
    CARGO_PROFILE_DEV_DEBUG=2 RUSTC_WRAPPER= cargo rustc --locked --offline "${flags[@]}" -- \
      --remap-path-prefix "$PWD=."
    node "$repo_root/rust/prod-codegen/tests/fixtures/scalar_length_wasm_test.mjs" \
      "$scratch/$output/target/wasm32-unknown-unknown/$profile/scalar_length_guest.wasm"
  done
done
for profile in debug release; do
  cmp "$scratch/first-guest/target/wasm32-unknown-unknown/$profile/scalar_length_guest.wasm" \
    "$scratch/second-guest/target/wasm32-unknown-unknown/$profile/scalar_length_guest.wasm"
done
cmp "$scratch/first-guest/generation-manifest.json" "$scratch/second-guest/generation-manifest.json"
echo 'Unicode scalar-length provenance, native complete scalar domain, bounded Wasm and deterministic generation passed'
