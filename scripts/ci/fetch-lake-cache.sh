#!/usr/bin/env bash
# Seed Lake's artifact cache from the `lake-cache` release (master's build products, published by the
# coordinator after each merge; docs/parallelism.md). Lake then fetches every module whose inputs match
# instead of compiling it. Best effort: any failure leaves a cold cache, never a failed job.
# Usage: scripts/ci/fetch-lake-cache.sh  (after elan is installed)
set -uo pipefail
repo=${GITHUB_REPOSITORY:-SolidiKeY/solidity-lean}
base="https://github.com/$repo/releases/download/lake-cache"
# Installs into Lake's own cache (LAKE_CACHE_DIR if set, else the toolchain's), the
# location `lake build` and every later step use; run it after elan is installed.
tmp=$(mktemp -d)
if curl -fsSL --retry 3 -o "$tmp/master-cache.tar.gz" "$base/master-cache.tar.gz" \
   && curl -fsSL --retry 3 -o "$tmp/master-cache.sha256" "$base/master-cache.sha256" \
   && (cd "$tmp" && sha256sum -c master-cache.sha256 >/dev/null) \
   && tar -C "$tmp" -xzf "$tmp/master-cache.tar.gz"; then
  PATH="$HOME/.elan/bin:$PATH" bash "$tmp/pack/install.sh" || echo "::warning::lake-cache install failed; building cold"
else
  echo "::warning::lake-cache release unavailable; building cold"
fi
rm -rf "$tmp"
