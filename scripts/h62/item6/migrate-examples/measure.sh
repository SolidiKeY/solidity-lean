#!/usr/bin/env bash
set -euo pipefail
[[ $# == 6 ]] || { echo "usage: measure.sh OFFICIAL PRIVATE_SYSROOT PRIVATE_CACHE EVIDENCE LABEL CACHE_ROOTS_JSON" >&2; exit 2; }
official=$(realpath "$1"); private=$(realpath "$2"); cache=$(realpath -m "$3"); evidence=$(realpath "$4"); label=$5; cache_roots=$(realpath "$6")
[[ $label =~ ^[a-zA-Z0-9_-]+$ ]] || exit 2
root=$(git rev-parse --show-toplevel); cd "$root"
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock -n 9 || { echo "writer busy" >&2; exit 2; }
[[ ! -e "$cache" && ! -e "$evidence/$label.json" ]] || { echo "refuse reused cache/result" >&2; exit 2; }
mkdir -p "$cache"
export PATH="$official/bin:$PATH"
export LEAN_NUM_THREADS=1 LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT="$private" LAKE_CACHE_DIR="$cache" LAKE_NO_CACHE=true
{
  git status --short; git rev-parse HEAD; lean --version; lake --version
  cat /sys/fs/cgroup/memory.max; cat /sys/fs/cgroup/memory.swap.max; cat /sys/fs/cgroup/cpu.max; getconf _NPROCESSORS_ONLN
} > "$evidence/$label-settings.txt"
git ls-files -z -- Solidity/Examples | xargs -0 sha256sum > "$evidence/$label-source-before.sha256"
git ls-files -z | xargs -0 sha256sum > "$evidence/$label-tree-before.sha256"
lake clean
python3 scripts/h62/item6/migrate-examples/cold-cache.py --roots "$cache_roots" --output "$evidence/$label-cache-prep.json"
set +e
python3 scripts/h62/item6/migrate-examples/bounded-run.py --output "$evidence/$label.json" -- lake build SolidityExamples
status=$?
set -e
git ls-files -z -- Solidity/Examples | xargs -0 sha256sum > "$evidence/$label-source-after.sha256"
git ls-files -z | xargs -0 sha256sum > "$evidence/$label-tree-after.sha256"
cmp "$evidence/$label-tree-before.sha256" "$evidence/$label-tree-after.sha256" || exit 3
cmp "$evidence/$label-source-before.sha256" "$evidence/$label-source-after.sha256" || exit 3
exit "$status"
