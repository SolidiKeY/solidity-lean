#!/usr/bin/env bash
# Both versions use identical clean private olean-only checks and resources.
set -euo pipefail
version=${1:?version required}; label=${2:?fresh output label required}
case "$version" in 4.24.0|4.35.0) ;; *) exit 2;; esac
[[ "$label" =~ ^[a-zA-Z0-9_-]+$ ]] || exit 2
root=$(git rev-parse --show-toplevel)
artifacts=/workspace/migrate-evm-artifacts
census=${3:-$artifacts/evidence/base-census.json}
[[ "$census" == "$artifacts"/* ]] || exit 2
[[ "$root" == /workspace/migrate-evm ]] || { echo 'wrong worktree'; exit 2; }
mkdir -p /tmp/solidity-lean-feature-groups-20261025
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock -n 9 || exit 3
git status --short
export PYTHONDONTWRITEBYTECODE=1
python3 scripts/h62/item6/migrate-evm/census.py "$root" "$artifacts/evidence/current-census.json"
cmp "$census" "$artifacts/evidence/current-census.json"
if [[ "$version" == 4.35.0 ]]; then
  python3 - <<'CHECK'
import hashlib,json
from pathlib import Path
p=json.loads(Path('/workspace/h62-coordinator-inputs/toolchain-pin.json').read_text())
f=Path('/workspace/migrate-evm-artifacts/toolchains')/p['asset']
assert hashlib.file_digest(f.open('rb'),'sha256').hexdigest()==p['sha256']
print('Coordinator official archive checksum PASS')
CHECK
fi
container="migrate-evm-$label"
cleanup() {
 env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH \
 docker --host=unix:///var/run/docker.sock rm -f "$container" >/dev/null 2>&1 || true
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH  docker --host=unix:///var/run/docker.sock run --rm --name "$container"  --network none --memory 12g --memory-swap 12g --cpus 1 --pids-limit 128 --user 1000:1000  --mount "type=bind,src=$root,dst=$root,readonly"  --mount "type=bind,src=$artifacts,dst=$artifacts"  --mount type=bind,src=/sys/fs/cgroup,dst=/run/outer-cgroup,readonly  --workdir "$root" -e PYTHONDONTWRITEBYTECODE=1  python@sha256:935c3c5b12357a7e10caa9c1e6ca5692344d97cf229832ef584be2cec9fc03df  python3 scripts/h62/item6/migrate-evm/bounded-build.py "$root"  "$artifacts/toolchains/lean-$version-linux" "$census"  "$artifacts/evidence/$label" 2>&1 | tee "$artifacts/evidence/$label-console.log" &
measurement_job=$!
wait "$measurement_job"
