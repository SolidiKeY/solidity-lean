#!/usr/bin/env bash
# Run only in this lane's attached cloud clone; no network is needed by checks.
set -euo pipefail
if [[ !( $# = 4 && $1 != retries ) && !( $# = 5 && $1 = retries ) ]]; then
  echo 'usage: run-solidity-baseline.sh corpus|cold|warm|retries COMPILER OUTPUT_DIR STARTING_COMMIT [SELECTION_JSON]' >&2
  exit 2
fi
mode=$1; compiler=$(realpath "$2"); output=$(realpath -m "$3"); base=$4; selection=${5:-}
if [[ -n "$selection" ]]; then selection=$(realpath "$selection"); fi
repo=$(git rev-parse --show-toplevel); cd "$repo"
case "$mode" in corpus|cold|warm|retries) ;; *) exit 2;; esac
mkdir -p /tmp/solidity-lean-feature-groups-20261025
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
git status --short
[[ -z "$(git ls-files --others --exclude-standard -- Solidity | rg '\.lean$')" ]] || { echo "Untracked Lean sources: inspect before exact-base run" >&2; exit 2; }
git diff --exit-code "$base" -- Solidity scripts/solidity-upstream.mjs scripts/solc-code.mjs >/dev/null
[[ ! -e "$output" ]] || { echo 'Refusing to overwrite evidence' >&2; exit 2; }
mkdir -p "$output/logs" "$repo/.lake/baseline-tools"
config="$repo/.baseline-lakefile.toml"
[[ ! -e "$config" ]] || { echo 'Existing baseline config: inspect before recovery' >&2; exit 2; }
name=""
managed_docker() {
 env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH docker --host=unix:///var/run/docker.sock "$@"
}
cleanup() {
 if [[ -n "$name" ]]; then
  local state
  if ! state=$(managed_docker inspect "$name" --format '{{.State.Running}}'); then
   echo "Container state unknown: preserve config/cache relocation; recover $name before further writes" >&2
   return 1
  fi
  if [[ "$state" = true ]]; then
   timeout -k 5 30 bash -c '''env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH docker --host=unix:///var/run/docker.sock stop -t 10 "$1"''' -- "$name" >/dev/null || return 1
   [[ "$(managed_docker inspect "$name" --format '{{.State.Running}}')" = false ]] || return 1
  fi
 fi
 rm -f "$config"
 if [[ -e .lake/baseline-saved-build ]]; then
  [[ -L .lake/build && "$(readlink .lake/build)" = baseline-cold/build ]] || { echo 'Cache restoration blocked: inspect .lake/build' >&2; return 1; }
  rm .lake/build
  mv .lake/baseline-saved-build .lake/build
 fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
python3 - "$repo" "$mode" "$base" <<'PY'
from pathlib import Path
import sys, json, hashlib
root=Path(sys.argv[1]); mode=sys.argv[2]
s=(root/'lakefile.toml').read_text().replace('version = "0.1.0"','version = "0.1.0"\nweakLeanArgs = ["-j1"]',1).replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
if mode in ('cold','warm'):
 s=s.replace('enableArtifactCache = true','enableArtifactCache = false')
 if mode=='cold' and (root/'.lake/baseline-cold/build').exists(): raise SystemExit('Cold directory exists; preserve it and choose another clone')
 if mode=='warm' and not (root/'.lake/baseline-cold/completed.json').exists(): raise SystemExit('No successful cold artifacts for warm measurement')
if mode in ('cold','warm'):
 h=hashlib.sha256()
 for p in sorted((root/'Solidity').rglob('*.lean'),key=lambda p: str(p)):
  h.update((str(p.relative_to(root))+'\0').encode()); h.update(p.read_bytes())
 fingerprint={'base':sys.argv[3],'modelSha256':h.hexdigest(),'configSha256':hashlib.sha256(s.encode()).hexdigest()}
 if mode=='warm':
  prior=json.loads((root/'.lake/baseline-cold/completed.json').read_text())
  if prior.get('exitCode')!=0 or prior.get('fingerprint')!=fingerprint: raise SystemExit('Cold provenance differs')
 build=root/'.lake/build'; saved=root/'.lake/baseline-saved-build'
 if saved.exists() or build.is_symlink(): raise SystemExit('Existing cache relocation: inspect before recovery')
 target=root/'.lake/baseline-cold/build'; target.mkdir(parents=True,exist_ok=True)
 build.rename(saved); build.symlink_to('baseline-cold/build',target_is_directory=True)
 (root/'.lake/baseline-cold/provenance.json').write_text(json.dumps(fingerprint,indent=2)+'\n')
(root/'.baseline-lakefile.toml').write_text(s)
wrapper=root/'.lake/baseline-tools/lake'
wrapper.write_text('''#!/bin/bash
set -e
real=/workspace/.setup/tools/lean-4.24.0-linux/bin/lake
if [[ " $* " == *" lean "* ]]; then
 if [[ " $* " == *" -- "* ]]; then
  exec "$real" -f /workspace/solidity-lean/.baseline-lakefile.toml "$@" -j1
 else
  exec "$real" -f /workspace/solidity-lean/.baseline-lakefile.toml "$@" -- -j1
 fi
fi
exec "$real" -f /workspace/solidity-lean/.baseline-lakefile.toml "$@"
'''); wrapper.chmod(0o755)
PY
cp "$config" "$output/lakefile.toml"
cp "$repo/.lake/baseline-tools/lake" "$output/lake-wrapper"
# Pinned local image: pull this digest beforehand using the managed daemon.
image=ubuntu@sha256:24737cef17f4e22b1977df7d9a05e77c4e28b7da5b8911f8d8ccda136bf3573c
name="solidity-baseline-${mode}-$$"
set +e
env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH \
 docker --host=unix:///var/run/docker.sock run --name "$name" --network none \
 --memory 12g --memory-swap 12g --cpus 1 --user "$(id -u):$(id -g)" \
 -v /workspace:/workspace -v /opt:/opt:ro -v /usr:/usr:ro -v /lib:/lib:ro -v /lib64:/lib64:ro -v /bin:/bin:ro \
 -w "$repo" "$image" /bin/bash -c '
set -u
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/usr/bin:/bin
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
export HOME=/workspace/solidity-lean/.lake/baseline-home
mkdir -p "$HOME/.elan/bin"
ln -sf /workspace/solidity-lean/.lake/baseline-tools/lake "$HOME/.elan/bin/lake"
export PATH=/workspace/solidity-lean/.lake/baseline-tools:$PATH
mode=$1; compiler=$2; output=$3; selection=$4
if [[ "$mode" = corpus || "$mode" = retries ]]; then
 python3 scripts/solidity-baseline-time.py "$output/logs/upstream-build" timeout -k 10 1800 lake build Solidity.Tools.Upstream || exit $?
 if [[ "$mode" = corpus ]]; then
  python3 scripts/solidity-baseline-time.py "$output/logs/corpus" node scripts/solidity-upstream.mjs run --compiler "$compiler" --out "$output/results"
 else
  python3 scripts/solidity-baseline-time.py "$output/logs/retries" python3 scripts/solidity-baseline-retries.py run "$selection" --compiler "$compiler" --out "$output/results"
 fi
else
 python3 scripts/solidity-baseline-time.py "$output/logs/$mode" timeout -k 10 5400 ./run-lean.sh
 code=$?
 exit "$code"
fi
' -- "$mode" "$compiler" "$output" "$selection"
code=$?
set -e
env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH docker --host=unix:///var/run/docker.sock inspect "$name" --format '{{json .State}}' >"$output/container-state.json"
printf '%s\n' "$code" >"$output/exit-code.txt"
if [[ "$mode" = cold && "$code" = 0 ]]; then
 python3 - "$output" <<'PYMARK'
import json,sys,hashlib
from pathlib import Path
p=Path('.lake/baseline-cold'); log=Path(sys.argv[1])/'logs/cold.json'
(p/'completed.json').write_text(json.dumps({'exitCode':0,'fingerprint':json.loads((p/'provenance.json').read_text()),'timingSha256':hashlib.sha256(log.read_bytes()).hexdigest()},indent=2)+'\n')
PYMARK
fi
# Retain the stopped container for inspect/recovery; no source results are removed.
exit "$code"
