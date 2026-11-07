#!/usr/bin/env bash
set -uo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]] || exit 2
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR= PYTHONDONTWRITEBYTECODE=1
export PATH="$PWD/.lake/native-browser-h40-full-bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
out=docs/benchmarks/directruntime-2026-11-04/h40/policy
mkdir -p "$out"
[[ ! -e $out/results.tsv ]] || exit 2
failed=0
run() {
 local name=$1; shift
 if "$@" >"$out/$name.log" 2>&1; then
  printf 'PASS\t%s\n' "$name" >>"$out/results.tsv"
 else
  failed=1; printf 'FAIL\t%s\n' "$name" >>"$out/results.tsv"
 fi
}
run trust bash scripts/check-trust.sh
run orphans node scripts/check-orphans.mjs
run layers node scripts/check-layers.mjs
run roots bash scripts/coord-tools/register.sh --check
run doc-paths bash scripts/check-doc-paths.sh
run axiom-pins node scripts/check-axiom-pins.mjs
run testsuite bash scripts/check-testsuite.sh
run automatic-strict node scripts/check-automatic.mjs --strict
run sort bash scripts/check-solkey.sh --key "$SOLKEY_RULES"
cat "$out/results.tsv"
exit "$failed"
