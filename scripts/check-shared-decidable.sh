#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/lean4-prod-shared-decidable.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
node "$repo_root/scripts/check-shared-decidable-provenance.mjs"
cd "$repo_root/lean"
lake build Conformance.LexLeanSharedDecidable ProdLib
lake env lean Conformance/SharedDecidable.lean
for output in first second; do
  lake exe prod-export --module Conformance.LexLeanSharedDecidable \
    --root SharedDecidableFixture.Main.choose \
    --root SharedDecidableFixture.Main.choosePhase \
    --root SharedDecidableFixture.Main.entry \
    --ir-module SharedConditional --out "$scratch/$output-export"
done
for artifact in kernel.ir roots.json coverage.json; do
  cmp "$scratch/first-export/$artifact" "$scratch/second-export/$artifact"
done
if grep -Eq '\(type "Decidable"|\(ctor "Decidable\.|\(alt "Decidable\.|\(extern |\(opaque ' "$scratch/first-export/kernel.ir"; then
  echo 'shared conditional export retained unsupported computation' >&2
  exit 1
fi
grep -Fq '(jp ' "$scratch/first-export/kernel.ir"
grep -Fq '(alt "Bool.false" ()' "$scratch/first-export/kernel.ir"
grep -Fq '(alt "Bool.true" ()' "$scratch/first-export/kernel.ir"
for output in first second; do
  cd "$repo_root/rust"
  RUSTC_WRAPPER= cargo run --locked --offline -p prod-cli -- cargo \
    "$scratch/first-export/kernel.ir" --output "$scratch/$output" \
    --name shared-decidable --version 0.1.0 \
    --description 'LexLean shared conditional compiler fixture' \
    --repository https://github.com/auser/lean4-prod \
    --homepage https://github.com/auser/lean4-prod \
    --readme "$repo_root/fixtures/lexlean-shared-decidable/README.md" \
    --license-mit "$repo_root/rust/prod-codegen/tests/fixtures/LICENSE-MIT" \
    --license-apache /usr/share/common-licenses/Apache-2.0
done
diff -ru "$scratch/first" "$scratch/second"
mkdir "$scratch/first/tests"
cp "$repo_root/rust/prod-codegen/tests/fixtures/shared_decidable_generated_test.rs" "$scratch/first/tests/shared.rs"
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
    --entry entry --export-name holo_run --input-allocation-cap 128 \
    --output-allocation-cap 3 --maximum-pages 4 --crate-name shared-decidable-guest
  cd "$scratch/$output"
  for profile in debug release; do
    flags=()
    if [ "$profile" = release ]; then flags+=(--release); fi
    CARGO_PROFILE_DEV_DEBUG=2 RUSTC_WRAPPER= cargo rustc --locked --offline "${flags[@]}" -- \
      --remap-path-prefix "$PWD=."
    node "$repo_root/rust/prod-codegen/tests/fixtures/shared_decidable_wasm_test.mjs" \
      "$scratch/$output/target/wasm32-unknown-unknown/$profile/shared_decidable_guest.wasm"
  done
done
for profile in debug release; do
  cmp "$scratch/first-guest/target/wasm32-unknown-unknown/$profile/shared_decidable_guest.wasm" \
    "$scratch/second-guest/target/wasm32-unknown-unknown/$profile/shared_decidable_guest.wasm"
done
cmp "$scratch/first-guest/generation-manifest.json" "$scratch/second-guest/generation-manifest.json"
echo 'Shared conditional provenance, proof-erasure refusals, native/no_std, bounded Wasm and deterministic generation passed'
