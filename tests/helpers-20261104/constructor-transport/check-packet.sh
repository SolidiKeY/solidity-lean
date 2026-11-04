#!/usr/bin/env bash
set -uo pipefail
cd /workspace/solidity-lean
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
out=tests/helpers-20261104/constructor-transport/final-gates
mkdir -p "$out"
: > "$out/gates.tsv"
failed=0
run() {
  local name=$1; shift
  local result=0 command
  printf -v command '%q ' "$@"
  command=${command% }
  bash tests/helpers-20261104/constructor-transport/bounded.sh "$@" > "$out/$name.log" 2>&1 || result=$?
  printf '%s	%s	%s
' "$name" "$result" "$command" >> "$out/gates.tsv"
  printf '%s EXIT=%s
' "$name" "$result"
  if [ "$result" -ne 0 ]; then failed=1; fi
}
run runtime /bin/bash -c 'set -e; printf "MEMORY_MAX="; cat /sys/fs/cgroup/memory.max; printf "SWAP_MAX="; cat /sys/fs/cgroup/memory.swap.max; lake --version; lean --version; lake env lean -j1 --tstack=131072 Solidity/KeySort.lean; echo "KeySort PASS; RUNTIME_GATE_PASS"'
run packet-build lake -f tests/helpers-20261104/constructor-transport/serial.toml build Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Controls
run axiom-pins lake env lean -j1 --tstack=131072 tests/helpers-20261104/constructor-transport/AxiomPins.lean
run controls-mcp /bin/bash -c 'export PATH=/workspace/solidity-lean/tests/helpers-20261104/constructor-transport/bin:$PATH; export LEAN_LSP_MAX_OPEN_FILES=1; trap "python3 scripts/coord-tools/lean-mcp stop" EXIT; python3 scripts/coord-tools/lean-mcp diag Solidity/Lowering/V08/HelperPackets/ConstructorTransport/Controls.lean'
run compiler node tests/helpers-20261104/constructor-transport/compiler-control.cjs
run full-gate /bin/bash run-lean.sh
exit "$failed"
