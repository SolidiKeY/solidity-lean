#!/usr/bin/env bash
set -uo pipefail
cd /workspace/solidity-lean
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
out=tests/helpers-20261104/constructor-transport/adoption-9584f9e7
: > "$out/gates.tsv"
failed=0
run() {
 local name=$1; shift
 local result=0 command
 printf -v command '%q ' "$@"; command=${command% }
 bash tests/helpers-20261104/constructor-transport/bounded.sh "$@" > "$out/$name.log" 2>&1 || result=$?
 printf '%s\t%s\t%s\n' "$name" "$result" "$command" >> "$out/gates.tsv"
 printf '%s EXIT=%s\n' "$name" "$result"
 if [ "$result" -ne 0 ]; then failed=1; fi
}
run runtime bash -c 'set -e; cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max; lean --version; lake --version; lake env lean -j1 --tstack=131072 Solidity/KeySort.lean; echo KeySort_PASS'
run owned-build lake -f tests/helpers-20261104/constructor-transport/serial.toml build Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Source Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Target Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Producer Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Controls
for module in Source Target Producer Controls; do
 run "kernel-$module" lake env lean -j1 --tstack=131072 "Solidity/Lowering/V08/HelperPackets/ConstructorTransport/$module.lean"
done
run axiom-pins lake env lean -j1 --tstack=131072 tests/helpers-20261104/constructor-transport/AxiomPins.lean
run axiom-inventory lake env lean -j1 --tstack=131072 tests/helpers-20261104/constructor-transport/h35/AxiomInventory.lean
run compiler-controls node tests/helpers-20261104/constructor-transport/compiler-control.cjs
exit "$failed"
