#!/usr/bin/env bash
set -euo pipefail
version=${1:?version}; cache=${2:?completed private cache}; label=${3:?output label}; source=${4:-tests/h62/item6/migrate-evm/ReadApi.lean}
[[ "$version" == 4.24.0 || "$version" == 4.35.0 ]] || exit 2
[[ "$source" == tests/h62/item6/migrate-evm/*.lean ]] || exit 2
[[ "$label" =~ ^[a-zA-Z0-9_-]+$ ]] || exit 2
root=/workspace/migrate-evm
artifacts=/workspace/migrate-evm-artifacts
census=${5:-$artifacts/evidence/base-census.json}
[[ "$census" == "$artifacts/evidence/"* ]] || exit 2
[[ "$cache" == "$artifacts/evidence/"* ]] || exit 2
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock -n 9 || exit 3
[[ ! -e "$artifacts/evidence/$label.jsonl" ]] || exit 2
python3 scripts/h62/item6/migrate-evm/validate-cache.py "$root" "$cache" "$version" "$census"
container="migrate-evm-$label"
cleanup() {
 env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH docker --host=unix:///var/run/docker.sock rm -f "$container" >/dev/null 2>&1 || true
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH docker --host=unix:///var/run/docker.sock run --rm --name "$container" --network none --memory 12g --memory-swap 12g --cpus 1 --pids-limit 128 --user 1000:1000 --mount "type=bind,src=$root,dst=$root,readonly" --mount "type=bind,src=$artifacts,dst=$artifacts" --mount type=bind,src=/sys/fs/cgroup,dst=/run/outer-cgroup,readonly --workdir "$root" -e LEAN_NUM_THREADS=1 -e "LEAN_PATH=$cache/lib" -i python@sha256:935c3c5b12357a7e10caa9c1e6ca5692344d97cf229832ef584be2cec9fc03df python3 - "$version" "$source" "$census" <<'CHECK' > "$artifacts/evidence/$label.jsonl" 2> "$artifacts/evidence/$label.stderr" &
import os,signal,subprocess,sys,time,json
from pathlib import Path
G=1024**3
cg=Path('/sys/fs/cgroup'); outer=Path('/run/outer-cgroup')
assert int((cg/'memory.max').read_text())==12*G
assert int((cg/'memory.swap.max').read_text())==0

def available():
    headroom=int((outer/'memory.max').read_text())-int((outer/'memory.current').read_text())
    mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])*1024
    return min(headroom,mem)>=4*G and int((outer/'memory.swap.current').read_text())==0

assert available(), 'reserve preflight'
toolchain='/workspace/migrate-evm-artifacts/toolchains/lean-'+sys.argv[1]+'-linux'
census=json.loads(Path(sys.argv[3]).read_text())
modules=[m for m,r in census['modules'].items() if r['assigned']]
child=subprocess.Popen([toolchain+'/bin/lean','--tstack=131072','-j1','--run',sys.argv[2],toolchain]+modules,start_new_session=True)
start=time.monotonic()
try:
    while child.poll() is None:
        if not available(): raise RuntimeError('RESOURCE_STOP')
        if time.monotonic()-start>300: raise RuntimeError('INVENTORY_300S_STOP')
        time.sleep(.1)
finally:
    if child.poll() is None:
        os.killpg(child.pid,signal.SIGTERM)
        try: child.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid,signal.SIGKILL); child.wait()
    try: os.killpg(child.pid,signal.SIGKILL)
    except ProcessLookupError: pass
raise SystemExit(child.returncode)
CHECK
inventory_job=$!
wait "$inventory_job"
