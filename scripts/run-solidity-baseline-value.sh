#!/usr/bin/env bash
# One authorized root-only refresh in a fresh private output; no Lake build.
set -euo pipefail
repo=$(realpath "$(git rev-parse --show-toplevel)")
[[ "$repo" = /workspace/solidity-lean && $# = 1 ]] || { echo 'usage from saved clone: scripts/run-solidity-baseline-value.sh FRESH_PRIVATE_OUTPUT'; exit 2; }
cd "$repo"
out=$(realpath -m "$1")
[[ "$out" = "$repo/.lake/"* && ! -e "$out" ]] || { echo 'fresh private output under attached clone .lake required'; exit 2; }
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
if pgrep -x lean >/dev/null || pgrep -x lake >/dev/null; then echo 'existing Lean/Lake worker: stop without interrupting it'; exit 2; fi
[[ $(awk '/MemAvailable/ {print $2}' /proc/meminfo) -ge 12582912 ]] || { echo '12GiB available-memory reserve unavailable'; exit 2; }
git diff --exit-code 29b73d0e -- Solidity Solidity.lean lakefile.toml docs/solidity-features.json >/dev/null
[[ -z "$(git ls-files --others --exclude-standard -- Solidity | rg '\.lean$' || true)" ]] || exit 2
# Restore only exact historical raw input prerequisites, never replace an existing file.
python3 - <<'PY'
from pathlib import Path
import tarfile,json,hashlib
base=Path('tests/upstream/baseline-20261028/native-cache');ledger=json.loads((base/'archive.json').read_text());archive=base/'evidence.tar.gz';assert hashlib.sha256(archive.read_bytes()).hexdigest()==ledger['sha256']
with tarfile.open(archive,'r:gz') as tf:
 for member in tf:
  if member.isfile() and (member.name=='FileHashes.lean' or member.name.startswith('runs/NativePositive/')):
   data=tf.extractfile(member).read();assert hashlib.sha256(data).hexdigest()==ledger['files'][member.name]['sha256']
   p=base/member.name
   if p.exists():assert p.read_bytes()==data
   else:
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('xb') as f:f.write(data)
PY
name="solidity-baseline-value-repro-$$"
managed_docker() { env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH docker --host=unix:///var/run/docker.sock "$@"; }
managed_docker run --name "$name" --network none --memory 12g --memory-swap 12g --cpus 1 --user "$(id -u):$(id -g)" \
 -v /workspace:/workspace -v /opt:/opt:ro -v /usr:/usr:ro -v /lib:/lib:ro -v /lib64:/lib64:ro -v /bin:/bin:ro -w "$repo" \
 ubuntu@sha256:24737cef17f4e22b1977df7d9a05e77c4e28b7da5b8911f8d8ccda136bf3573c /bin/bash -c '
set -euo pipefail
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/usr/bin:/bin
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 BASELINE_VALUE_BASE="$1"
python3 scripts/solidity-baseline-lifetime-root.py "$1"
python3 scripts/solidity-baseline-value-runtime.py
python3 scripts/solidity-baseline-value-verify.py "$1" --out "$1/verification.json"
' -- "$out"
