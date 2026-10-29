#!/usr/bin/env bash
# Run every hand-written scripts/check-*.mjs EVM vector check once per pinned
# compiler. Optional reference tooling; not a Lean dependency.
#
# Usage: scripts/evm-vectors/run.sh SOLJSON_0_8_38 SOLJSON_0_8_34 OUT_DIR [NODE_MODULES]
# NODE_MODULES defaults to scripts/evm-vectors/node_modules, installed with
#   npm ci --ignore-scripts --prefix scripts/evm-vectors
# Each check writes OUT_DIR/<name>.log. check-self-power-data.mjs also writes
# OUT_DIR/compiler-evm.json, and the transient-world log is its JSON report.
# Exit 0 = every check passed.
set -u
cd "$(dirname "$0")/../.."
[ $# -ge 3 ] || { sed -n 5,10p "$0"; exit 2; }
c38=$(realpath "$1"); c34=$(realpath "$2"); out=$3
modules=$(realpath "${4:-scripts/evm-vectors/node_modules}")
h38=6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390
h34=c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8
mkdir -p "$out"; out=$(realpath "$out"); failed=0
run() {
  local name=$1; shift
  if node "$@" > "$out/$name.log" 2>&1; then echo "PASS $name | $(tail -1 "$out/$name.log" | cut -c1-160)"
  else failed=$((failed + 1)); echo "FAIL $name | $(grep -m1 -i 'error' "$out/$name.log" | cut -c1-160)"; fi
}
run abi-vectors scripts/check-abi-vectors.mjs "$c38" "$modules"
run recursive-types scripts/check-recursive-types.mjs "$c38" "$modules"
run self-power-data scripts/check-self-power-data.mjs "$c38" "$modules" "$out/compiler-evm.json"
run modifier-frames scripts/check-modifier-frames.mjs "$c38" "$modules"
run operator-aliases scripts/check-operator-aliases.mjs "$c38" "$modules"
run slice-copies scripts/check-slice-copies.mjs "$c38" "$h38" "$modules"
for v in 38 34; do
  c=c$v; h=h$v
  run public-getters-$v scripts/check-public-getters.mjs "${!c}" "$modules"
  run call-exception-$v scripts/check-call-exception-vectors.mjs "${!c}" "$modules"
  run transient-$v scripts/check-transient-vectors.mjs "${!c}" "$modules"
  run source-admission-$v scripts/check-source-admission.mjs "${!c}" "${!h}" "$modules"
done
run transient-world scripts/check-transient-world-vectors.mjs "$c38" "$modules"
run abi-hex-call scripts/check-abi-hex-call.mjs "$modules" "$c38" "$c34"
echo "$((16 - failed))/16 checks passed"
[ "$failed" -eq 0 ]
