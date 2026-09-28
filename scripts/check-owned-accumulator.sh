#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/lean4-prod-owned-accumulator.XXXXXXXX")
cleanup() {
  local status=$?
  if [ "$status" -eq 0 ]; then
    rm -rf -- "$scratch"
  else
    printf 'Owned accumulator failure evidence retained at %s\n' "$scratch" >&2
  fi
  exit "$status"
}
trap cleanup EXIT
node "$repo_root/scripts/check-owned-accumulator-provenance.mjs"
cd "$repo_root/lean"
lake build Conformance.LexLeanOwnedAccumulator ProdLib
for output in first second; do
  lake exe prod-export --module Conformance.LexLeanOwnedAccumulator \
    --root OwnedAccumulatorFixture.Main.collect --root OwnedAccumulatorFixture.Main.entry \
    --root OwnedAccumulatorFixture.Main.finish \
    --ir-module OwnedAccumulator --out "$scratch/$output-export"
done
for artifact in kernel.ir roots.json coverage.json; do
  cmp "$scratch/first-export/$artifact" "$scratch/second-export/$artifact"
done
rg -Fq '(append ' "$scratch/first-export/kernel.ir"
rg -Fq '(length ' "$scratch/first-export/kernel.ir"

for output in first second; do
  cd "$repo_root/rust"
  RUSTC_WRAPPER= cargo run --locked --offline -p prod-cli -- cargo \
    "$scratch/first-export/kernel.ir" --output "$scratch/$output" \
    --name owned-accumulator-fixture --version 0.1.0 \
    --description 'LexLean owned list accumulator compiler fixture' \
    --repository https://github.com/auser/lean4-prod \
    --homepage https://github.com/auser/lean4-prod \
    --readme "$repo_root/fixtures/lexlean-owned-accumulator/README.md" \
    --license-mit "$repo_root/rust/prod-codegen/tests/fixtures/LICENSE-MIT" \
    --license-apache /usr/share/common-licenses/Apache-2.0
done
diff -ru "$scratch/first" "$scratch/second"
mkdir "$scratch/first/tests"
cp "$repo_root/rust/prod-codegen/tests/fixtures/owned_accumulator_generated_test.rs" "$scratch/first/tests/owned.rs"
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
    --entry entry --export-name holo_run --input-allocation-cap 67108864 \
    --output-allocation-cap 67108864 --maximum-pages 16384 --crate-name owned-accumulator-guest
  cd "$scratch/$output"
  for profile in debug release; do
    flags=()
    if [ "$profile" = release ]; then flags+=(--release); fi
    # Keep debug information while removing the temporary build-directory identity.
    # cargo rustc appends this flag without replacing the bounded Wasm linker flags.
    CARGO_PROFILE_DEV_DEBUG=2 RUSTC_WRAPPER= cargo rustc --locked --offline "${flags[@]}" -- \
      --remap-path-prefix "$PWD=."
    node "$repo_root/rust/prod-codegen/tests/fixtures/owned_accumulator_wasm_test.mjs" \
      "$scratch/$output/target/wasm32-unknown-unknown/$profile/owned_accumulator_guest.wasm"
  done
done
for profile in debug release; do
  cmp "$scratch/first-guest/target/wasm32-unknown-unknown/$profile/owned_accumulator_guest.wasm" \
    "$scratch/second-guest/target/wasm32-unknown-unknown/$profile/owned_accumulator_guest.wasm"
done
cmp "$scratch/first-guest/generation-manifest.json" "$scratch/second-guest/generation-manifest.json"
echo 'Owned accumulator source provenance, exact 64 MiB native/Wasm and deterministic generation passed'
