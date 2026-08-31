#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
fixture="$repo_root/fixtures/lexlean-1.1"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/lean4-prod-named.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT

first="$scratch/first"
second="$scratch/second"
mkdir -p "$first" "$second"

cd "$repo_root/lean"
lake build Conformance.LexLean11 Conformance.BadRoots

export_once() {
  local out=$1
  lake exe prod-export \
    --module Conformance.LexLean11 \
    --root SemanticFixture.Main.allConsecutive \
    --ir-module SemanticFixture \
    --out "$out"
}

export_once "$first"
export_once "$second"

for artifact in kernel.ir roots.json coverage.json; do
  cmp "$first/$artifact" "$second/$artifact"
  cmp "$first/$artifact" "$fixture/expected/$artifact"
done

cd "$repo_root/rust"
cargo run -p prod-cli -- validate "$first/kernel.ir"
cargo run -p prod-cli -- gen "$first/kernel.ir" --output "$first/generated.rs"
cargo run -p prod-cli -- gen "$second/kernel.ir" --output "$second/generated.rs"
cmp "$first/generated.rs" "$second/generated.rs"
cmp "$first/generated.rs" "$fixture/expected/generated.rs"

expect_failure() {
  local expected=$1
  shift
  local stderr="$scratch/failure.stderr"
  if "$@" >"$scratch/failure.stdout" 2>"$stderr"; then
    echo "expected command to fail: $*" >&2
    exit 1
  fi
  grep -F -- "$expected" "$stderr" >/dev/null
}

cd "$repo_root/lean"
expect_failure "named export requires at least one --root" \
  lake exe prod-export --module Conformance.BadRoots --ir-module Bad --out "$scratch/bad"
expect_failure "duplicate root Conformance.BadRoots.alpha" \
  lake exe prod-export --module Conformance.BadRoots \
    --root Conformance.BadRoots.alpha --root Conformance.BadRoots.alpha \
    --ir-module Bad --out "$scratch/bad"
expect_failure "roots are not strictly sorted" \
  lake exe prod-export --module Conformance.BadRoots \
    --root Conformance.BadRoots.zeta --root Conformance.BadRoots.alpha \
    --ir-module Bad --out "$scratch/bad"
expect_failure "root Conformance.BadRoots.missing is missing" \
  lake exe prod-export --module Conformance.BadRoots \
    --root Conformance.BadRoots.missing --ir-module Bad --out "$scratch/bad"
expect_failure "root Conformance.BadRoots.theoremRoot is theorem-only" \
  lake exe prod-export --module Conformance.BadRoots \
    --root Conformance.BadRoots.theoremRoot --ir-module Bad --out "$scratch/bad"
expect_failure "root Conformance.BadRoots.unsafeRoot is unsafe" \
  lake exe prod-export --module Conformance.BadRoots \
    --root Conformance.BadRoots.unsafeRoot --ir-module Bad --out "$scratch/bad"
expect_failure "root Conformance.BadRoots.partialRoot is opaque, partial, or noncomputable" \
  lake exe prod-export --module Conformance.BadRoots \
    --root Conformance.BadRoots.partialRoot --ir-module Bad --out "$scratch/bad"
expect_failure "root Conformance.BadRoots.noncomputableRoot is opaque, partial, or noncomputable" \
  lake exe prod-export --module Conformance.BadRoots \
    --root Conformance.BadRoots.noncomputableRoot --ir-module Bad --out "$scratch/bad"
expect_failure "root Conformance.BadRoots.typeValuedRoot does not generate code" \
  lake exe prod-export --module Conformance.BadRoots \
    --root Conformance.BadRoots.typeValuedRoot --ir-module Bad --out "$scratch/bad"

echo "named-export conformance passed"
