#!/usr/bin/env bash
# Seed Lake's artifact cache from the `lake-cache` release (master's build products, published by the
# coordinator after each merge; docs/parallelism.md). Lake then fetches every module whose inputs match
# instead of compiling it. Best effort: any failure leaves a cold cache, never a failed job.
# Usage: scripts/ci/fetch-lake-cache.sh  (after elan is installed)
# The pack is published in parts (a release asset is at most 2 GiB): master-cache.parts names the parts and
# the sha256 of the whole tar.gz. Without that manifest, the older single asset master-cache.tar.gz is used.
set -uo pipefail
repo=${GITHUB_REPOSITORY:-SolidiKeY/solidity-lean}
base=${LAKE_CACHE_BASE:-"https://github.com/$repo/releases/download/lake-cache"}
# Installs into Lake's own cache (LAKE_CACHE_DIR if set, else the toolchain's), the
# location `lake build` and every later step use; run it after elan is installed.
tmp=$(mktemp -d)
get() { curl -fsSL --retry 3 -o "$tmp/$2" "$base/$1"; }
# Parts: the manifest's first line is "<sha256>  master-cache.tar.gz", then one part name per line.
parts() {
  curl -fsL --retry 3 -o "$tmp/master-cache.parts" "$base/master-cache.parts" || return 1   # absent: older single asset
  : > "$tmp/master-cache.tar.gz"
  tail -n +2 "$tmp/master-cache.parts" | while read -r p; do
    [ -n "$p" ] || continue
    case "$p" in *[!A-Za-z0-9._-]*) return 1;; esac
    get "$p" part && cat "$tmp/part" >> "$tmp/master-cache.tar.gz" && rm -f "$tmp/part" || return 1
  done || return 1
  head -n 1 "$tmp/master-cache.parts" > "$tmp/master-cache.sha256"
}
single() { get master-cache.tar.gz master-cache.tar.gz && get master-cache.sha256 master-cache.sha256; }
# The coordinator republishes after each merge by swapping assets; retry a missing asset or a
# checksum mismatch (seconds-wide swap window) a few times before building cold.
got=0
for attempt in 1 2 3 4; do
  if { parts || single; } && (cd "$tmp" && sha256sum -c master-cache.sha256 >/dev/null); then got=1; break; fi
  echo "lake-cache: attempt $attempt failed; retrying in ${LAKE_CACHE_RETRY_S:-30} s" >&2; sleep "${LAKE_CACHE_RETRY_S:-30}"
done
if [ "$got" = 1 ] && tar -C "$tmp" -xzf "$tmp/master-cache.tar.gz"; then
  root=$(git rev-parse --show-toplevel 2>/dev/null || pwd)
  (cd "$root" && PATH="$HOME/.elan/bin:$PATH" bash "$tmp/pack/install.sh") || echo "::warning::lake-cache install failed; building cold"
else
  echo "::warning::lake-cache release unavailable; building cold"
fi
rm -rf "$tmp"
