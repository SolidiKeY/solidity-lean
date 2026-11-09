#!/usr/bin/env bash
# Delete the repository's Actions caches whose key starts with PREFIX and that were created
# before the entry KEEP, so a cache family keeps one live entry (lean.yml, master only).
# Does nothing unless KEEP exists, so a failed save never leaves the family empty; an entry
# newer than KEEP (a later master run that finished first) is kept.
# Needs gh and GH_TOKEN with `actions: write`. Usage: evict-caches.sh PREFIX KEEP
# Exit 0 on success or nothing to do; 1 if listing or a deletion failed; 2 on usage error.
set -uo pipefail
[ $# -eq 2 ] && [ -n "$1" ] && [ -n "$2" ] || { echo "usage: evict-caches.sh PREFIX KEEP" >&2; exit 2; }
prefix=$1 keep=$2
case "$keep" in "$prefix"*) ;; *) echo "evict-caches: KEEP must start with PREFIX" >&2; exit 2;; esac
list=$(gh cache list --key "$prefix" --limit 100 --json id,key,createdAt,sizeInBytes) || exit 1
victims=$(python3 -c '
import json, sys
prefix, keep = sys.argv[1], sys.argv[2]
rows = [r for r in json.load(sys.stdin) if r["key"].startswith(prefix)]
kept = [r for r in rows if r["key"] == keep]
if not kept:
    print("evict-caches: %s not saved; nothing evicted" % keep, file=sys.stderr); sys.exit(0)
newest = max(r["createdAt"] for r in kept)
for r in rows:
    if r["key"] != keep and r["createdAt"] < newest:
        print(r["id"], r["key"], r["sizeInBytes"])
' "$prefix" "$keep" <<<"$list") || exit 1
status=0
while read -r id key size; do
  [ -n "$id" ] || continue
  if gh cache delete "$id"; then echo "evicted $key ($((size / 1048576)) MiB)"; else status=1; fi
done <<<"$victims"
exit "$status"
