#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd -P)
manifest="$repo_root/fixtures/prismpm-1.1/fixture-manifest.toml"

mapfile -t source_paths < <(sed -n 's/^source_path = "\([^"]*\)"$/\1/p' "$manifest")
mapfile -t source_hashes < <(sed -n 's/^source_sha256 = "\([0-9a-f]*\)"$/\1/p' "$manifest")
mapfile -t generated_paths < <(sed -n 's/^generated_path = "\([^"]*\)"$/\1/p' "$manifest")
mapfile -t generated_hashes < <(sed -n 's/^generated_sha256 = "\([0-9a-f]*\)"$/\1/p' "$manifest")

test "${#source_paths[@]}" -eq 4
test "${#source_hashes[@]}" -eq "${#source_paths[@]}"
test "${#generated_paths[@]}" -eq "${#source_paths[@]}"
test "${#generated_hashes[@]}" -eq "${#source_paths[@]}"

for index in "${!source_paths[@]}"; do
  printf '%s  %s\n' "${source_hashes[$index]}" "$repo_root/${source_paths[$index]}" | sha256sum -c -
  printf '%s  %s\n' "${generated_hashes[$index]}" "$repo_root/${generated_paths[$index]}" | sha256sum -c -
done

if grep -En '\<(sorry|admit|axiom|opaque)\>' "${generated_paths[@]/#/$repo_root/}"; then
  echo "generated Prism fixture contains a forbidden declaration" >&2
  exit 1
fi

echo "generated-fixture provenance passed"
