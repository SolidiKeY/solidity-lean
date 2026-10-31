#!/usr/bin/env bash
# Validate every owned target through Lake's source/toolchain-keyed cache, then
# import every source/toolchain/dependency-keyed, kernel-checked fixture.
# Cold fixture preparation is separate and bounded; missing/stale caches FAIL.
# This is NOT the raw-source sweep or
# the repository full gate. Do not raise its external120s/resource bound.
set -euo pipefail
out=${1:?absolute evidence directory required}
[[ "$out" = /* && -d "$out" ]] || { echo "existing absolute evidence directory required" >&2; exit 2; }
modules=()
for file in Solidity/Backend/InternalFlow/*.lean; do
  module=${file%.lean}
  modules+=("${module//\//.}")
done
# Fixture-only imports must also be refreshed by Lake before direct checks.
for file in tests/internal-flow/*.lean; do
  while read -r -a words; do
    [[ "${words[0]:-}" == import ]] || continue
    for imported in "${words[@]:1}"; do
      [[ "$imported" == -- ]] && break
      if [[ "$imported" == Solidity.* ]]; then
        modules+=("$imported")
      fi
    done
  done < "$file"
done
lake build "${modules[@]}" > "$out/cached-owned-imports.log" 2>&1
for file in tests/internal-flow/*.lean; do
  name=$(basename "$file" .lean)
  node tests/internal-flow/fixture-cache.mjs check "$file" "$out" > "$out/cached-$name-cache.log" 2>&1
done
