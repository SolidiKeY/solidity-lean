#!/usr/bin/env bash
# Isolated official-toolchain checks: no v4.24 cache, no source writes.
set -euo pipefail
mode=${1:?usage: bounded-check.sh keysort|imports|audit|timing}
case "$mode" in keysort|imports|audit|timing) ;; *) exit 2 ;; esac
repo=$(git rev-parse --show-toplevel)
evidence=${H62_AUDIT_EVIDENCE:-/workspace/h62-audit-evidence}
toolchain="$evidence/toolchain/lean-4.35.0-linux"
mkdir -p "$evidence"
archive="$evidence/toolchain/lean-4.35.0-linux.tar.zst"
expected=7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d
actual=$(sha256sum "$archive")
[[ ${actual%% *} == "$expected" ]] || { echo 'toolchain archive hash mismatch'; exit 2; }
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock -n 9
[[ $(awk '/MemAvailable/{print $2}' /proc/meminfo) -gt 4194304 ]] || { echo 'host headroom below 4GiB'; exit 2; }
vm_limit=$(cat /sys/fs/cgroup/memory.max)
vm_current=$(cat /sys/fs/cgroup/memory.current)
[[ $vm_limit =~ ^[0-9]+$ && $vm_current =~ ^[0-9]+$ ]] || exit 2
[[ $((vm_limit-vm_current)) -gt 4294967296 ]] || { echo 'effective VM headroom below 4GiB'; exit 2; }
proof_before=$(sha256sum "$repo/tests/h62/item2/audit-exact-verification/VisitedSetAudit.lean")
git status --short > "$evidence/status-$mode.txt"
set +e
env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH  docker --host=unix:///var/run/docker.sock run --rm -i  --memory=12g --memory-swap=12g --cpus=1 --network=none  -e LEAN_NUM_THREADS=1 -e LEAN_PATH=/evidence/build435  --mount "type=bind,src=$toolchain,dst=/lean,readonly"  --mount "type=bind,src=$repo,dst=/repo,readonly"  --mount type=bind,src=/sys/fs/cgroup,dst=/vm-cgroup,readonly --mount "type=bind,src=$evidence,dst=/evidence" -w /repo  ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852  bash -s -- "$mode" > "$evidence/bounded-$mode.log" 2>&1 <<'INNER'
set -euo pipefail
[[ $(cat /sys/fs/cgroup/memory.max) == 12884901888 ]]
[[ $(cat /sys/fs/cgroup/memory.swap.max) == 0 ]]
echo 'LIMITS memory.max=12884901888 memory.swap.max=0 LEAN_NUM_THREADS=1'
/lean/bin/lean --version
/lean/bin/lake --version
reserve_ok() {
 local vm_limit vm_current
 vm_limit=$(cat /vm-cgroup/memory.max)
 vm_current=$(cat /vm-cgroup/memory.current)
 [[ $vm_limit =~ ^[0-9]+$ && $vm_current =~ ^[0-9]+$ ]] || return 1
 [[ $(awk '/MemAvailable/{print $2}' /proc/meminfo) -gt 4194304 && $((vm_limit-vm_current)) -gt 4294967296 ]]
}
run_lean() {
 reserve_ok || { echo 'RESOURCE_STOP initial effective headroom'; return 2; }
 timeout 300 /lean/bin/lean -j1 --tstack=131072 "$@" &
 local job=$!
 while kill -0 "$job" 2>/dev/null; do
  if ! reserve_ok; then
   echo 'RESOURCE_STOP available memory reached 4GiB reserve'
   kill -TERM "$job" 2>/dev/null || true
   wait "$job" || true
   return 2
  fi
  sleep 0.1
 done
 wait "$job"
}
compile() {
 local module=$1
 [[ $(awk '/MemAvailable/{print $2}' /proc/meminfo) -gt 4194304 ]]
 mkdir -p "/evidence/build435/$(dirname "$module")"
 echo "CHECK $module $(date +%s.%N)"
 run_lean -o "/evidence/build435/$module.olean" "$module.lean"
 echo "PASS $module $(date +%s.%N)"
}
audit() {
 echo "AUDIT_START $(date +%s.%N)"
 run_lean tests/h62/item2/audit-exact-verification/VisitedSetAudit.lean
 echo "AUDIT_PASS $(date +%s.%N)"
}
case "$1" in
 keysort) compile Solidity/KeySort ;;
 imports) while read -r module; do compile "$module"; done < /evidence/import-plan.txt ;;
 audit) compile Solidity/Calculus/VisitedSet; audit ;;
 timing)
  echo PHASE_BEFORE
  for sample in 1 2 3 4 5; do compile Solidity/Calculus/VisitedSet; done
  audit
  echo PHASE_AFTER
  for sample in 1 2 3 4 5; do compile Solidity/Calculus/VisitedSet; done
  ;;
esac
echo "COMPLETED $1"
INNER
result=$?
set -e
if [[ $result -eq 0 ]] && ! rg -qx "COMPLETED $mode" "$evidence/bounded-$mode.log"; then
 result=2
 echo 'missing workload-completion marker; rejected empty/incomplete execution'
fi
if [[ $result -eq 0 ]] && [[ $mode == audit || $mode == timing ]]; then
 proof_after=$(sha256sum "$repo/tests/h62/item2/audit-exact-verification/VisitedSetAudit.lean")
 [[ $proof_before == "$proof_after" ]] || result=2
 if [[ $result -eq 0 ]]; then
  python3 - "$repo" "$evidence" "$mode" <<'RECEIPT'
import hashlib, json, sys
from pathlib import Path
repo, evidence, mode = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
proof = "tests/h62/item2/audit-exact-verification/VisitedSetAudit.lean"
module = "Solidity/Calculus/VisitedSet.lean"
log = f"bounded-{mode}.log"
hashfile = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipt = dict(schema=1, mode=mode, exit=0, proof_file=proof,
 proof_sha256=hashfile(repo/proof), interface_file=module,
 interface_sha256=hashfile(repo/module), log=log, log_sha256=hashfile(evidence/log),
 command=f"bash scripts/h62/item2/audit-exact-verification/bounded-check.sh {mode}",
 runner_sha256=hashfile(repo/"scripts/h62/item2/audit-exact-verification/bounded-check.sh"),
 reserve_monitor="host MemAvailable and outer memory.max-current, 0.1s, no reclaimable-cache credit",
 toolchain="leanprover/lean4:v4.35.0", archive_sha256="7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d")
(evidence/f"bounded-{mode}.receipt.json").write_text(json.dumps(receipt, indent=2)+"\n")
RECEIPT
 fi
fi
printf '%s\n' "$result" > "$evidence/bounded-$mode.exit"
printf '%s exit=%s evidence=%s\n' "$mode" "$result" "$evidence/bounded-$mode.log"
exit "$result"
