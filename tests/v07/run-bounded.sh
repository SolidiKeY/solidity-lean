#!/bin/sh
# H1: 4 GiB free-RAM reserve; unchanged aggregate 12 GiB/no-swap cap.
set -eu
repo=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$repo"
test "$#" -ge 2
label=$1
shift
case "$label" in ''|*[!a-zA-Z0-9-]*) exit 2;; esac
out=/workspace/v07-evidence/restart-20261102
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock -n 9
awk '/^MemAvailable:/ {if ($2<4194304) exit 1}' /proc/meminfo
test ! -e "$out/$label.log"
set -C
python3 - "$@" > "$out/$label.sh" <<'PY'
import sys,shlex
print('set -eu\nexport LEAN_NUM_THREADS=1')
args=sys.argv[1:]
if args[0]=='--run':
 print('lake --no-cache -f lakefile.v07.toml env lean --tstack=131072 -j1 --run '+' '.join(map(shlex.quote,args[1:])))
elif args[0]=='--files':
 for f in args[1:]:print('lake --no-cache -f lakefile.v07.toml env lean --tstack=131072 -j1 '+shlex.quote(f))
else:
 for m in args:print('lake --no-cache -f lakefile.v07.toml build '+shlex.quote(m))
PY
docker_local() {
 env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH docker --host=unix:///var/run/docker.sock "$@"
}
docker_local inspect v07-h2-reusable > "$out/$label-container.json"
python3 - "$out/$label-container.json" <<'PY'
import json,sys
c=json.load(open(sys.argv[1]))[0];h=c['HostConfig']
assert c['State']['Running'] and h['Memory']==12884901888 and h['MemorySwap']==12884901888
assert h['NanoCpus']==1000000000 and h['NetworkMode']=='none'
assert c['Image']=='sha256:354cdc53abb843ea02e9a72c153b000c290014d8a90aba62897c143710a5667f'
assert c['Config']['WorkingDir']=='/workspace/v07-lowering'
m={x['Destination']:x for x in c['Mounts']}
for p in ['/workspace/v07-lowering','/workspace/solidity-lean']:
 assert m[p]['Source']==p
assert m['/workspace/v07-lowering']['RW'] and not m['/workspace/solidity-lean']['RW']
assert m['/toolchain']['Source']=='/workspace/.setup/tools/lean-4.24.0-linux' and not m['/toolchain']['RW']
PY
docker_local exec v07-h2-reusable sh -c '
 test "$(cat /sys/fs/cgroup/memory.max)" = 12884901888 || exit 78
 test "$(cat /sys/fs/cgroup/memory.swap.max)" = 0 || exit 78
 cat /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.swap.max
 cat /proc/self/cgroup
 lean --version
 lake --version
 sh tests/v07/sample-memory.sh > "/evidence/restart-20261102/$1-rss.tsv" &
 monitor=$!
 sh "/evidence/restart-20261102/$1.sh"
 result=$?
 kill "$monitor"
 signal_result=$?
 wait "$monitor"
 monitor_result=$?
 printf "sampler_signal_exit %s\nsampler_exit %s\n" "$signal_result" "$monitor_result"
 cat /sys/fs/cgroup/memory.events /sys/fs/cgroup/memory.peak /sys/fs/cgroup/memory.swap.current
 if test "$result" -eq 0; then
  test "$signal_result" -eq 0 || exit "$signal_result"
  test "$monitor_result" -eq 0 || exit "$monitor_result"
 fi
 exit "$result"
' gate "$label" > "$out/$label.log" 2>&1
