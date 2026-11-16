#!/usr/bin/env bash
# Delete the repository's Actions caches whose key starts with PREFIX and ends in the SHA of
# a commit that KEEP's commit descends from, so a cache family keeps the entry of the newest
# master commit only (lean.yml `bridge-cache-evict`, master only). Keys end in "-<sha>".
# Does nothing unless KEEP exists, so a failed save never leaves the family empty; an entry
# of a newer or unrelated commit (a later master run that finished first) is kept.
# Needs gh, GH_TOKEN with `actions: write` and GH_REPO. Usage: evict-caches.sh PREFIX KEEP
# Exit 0 on success or nothing to do; 1 if listing or a deletion failed; 2 on usage error.
set -uo pipefail
[ $# -eq 2 ] && [ -n "$1" ] && [ -n "$2" ] || { echo "usage: evict-caches.sh PREFIX KEEP" >&2; exit 2; }
prefix=$1 keep=$2
case "$keep" in "$prefix"*-*) ;; *) echo "evict-caches: KEEP must start with PREFIX and end in -<sha>" >&2; exit 2;; esac
: "${GH_REPO:?evict-caches: GH_REPO not set}"
keep_sha=${keep##*-}
list=$(gh cache list --key "$prefix" --limit 100 --json id,key,sizeInBytes) || exit 1
rows=$(python3 -c '
import json, sys
prefix, keep = sys.argv[1], sys.argv[2]
rows = [r for r in json.load(sys.stdin) if r["key"].startswith(prefix)]
if not any(r["key"] == keep for r in rows):
    print("evict-caches: %s not saved; nothing evicted" % keep, file=sys.stderr); sys.exit(0)
for r in rows:
    if r["key"] != keep:
        print(r["id"], r["key"], r["sizeInBytes"])
' "$prefix" "$keep" <<<"$list") || exit 1
status=0
while read -r id key size; do
  [ -n "$id" ] || continue
  sha=${key##*-}
  # "ahead": KEEP's commit descends from this entry's commit.
  rel=$(gh api "repos/$GH_REPO/compare/$sha...$keep_sha" --jq .status </dev/null 2>/dev/null) || rel=unknown
  if [ "$rel" != ahead ]; then echo "kept $key ($rel relative to $keep_sha)"; continue; fi
  if gh cache delete "$id" </dev/null; then echo "evicted $key ($((size / 1048576)) MiB)"; else status=1; fi
done <<<"$rows"
exit "$status"
