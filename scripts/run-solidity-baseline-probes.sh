#!/usr/bin/env bash
# Reproduce ONLY compiler/provenance/source-reader diagnostics, without a build.
set -euo pipefail
repo=$(realpath "$(git rev-parse --show-toplevel)")
[[ "$repo" = /workspace/solidity-lean && $# = 1 ]] || { echo 'usage from attached clone: scripts/run-solidity-baseline-probes.sh FRESH_OUTPUT'; exit 2; }
cd "$repo"
output=$(realpath -m "$1")
[[ "$output" = "$repo/"* && ! -e "$output" ]] || { echo 'fresh output under attached clone required'; exit 2; }
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
git status --short
git diff --exit-code 13edcbe4 -- Solidity Solidity.lean lakefile.toml scripts/solc-ast.mjs scripts/solc-code.mjs >/dev/null
[[ -z "$(git ls-files --others --exclude-standard -- Solidity | rg '\.lean$')" ]] || { echo 'Untracked core Lean source: inspect before probes'; exit 2; }
config="$repo/.diagnostic-lakefile.toml"
[[ ! -e "$config" ]] || { echo 'Existing session config: inspect owner first'; exit 2; }
mkdir -p "$output/logs" "$repo/.lake/diagnostic-tools"
python3 - "$output" <<'INPUTS'
import hashlib,json,sys,tarfile
from pathlib import Path
source=Path('tests/upstream/baseline-20261028/probes');archive=source/'evidence.tar.gz';ledger=json.loads((source/'archive.json').read_text())
assert hashlib.sha256(archive.read_bytes()).hexdigest()==ledger['sha256']
output=Path(sys.argv[1]);(output/'inputs').mkdir()
with tarfile.open(archive,'r:gz') as tf:
 for member in tf:
  if member.isfile() and member.name.startswith('inputs/'):
   assert len(Path(member.name).parts)==2
   data=tf.extractfile(member).read();assert hashlib.sha256(data).hexdigest()==ledger['files'][member.name]['sha256']
   (output/'inputs'/Path(member.name).name).write_bytes(data)
INPUTS
cp tests/upstream/baseline-20261028/probes/lakefile.toml "$config"
cp "$config" "$output/lakefile.toml"
cat > "$repo/.lake/diagnostic-tools/lake" <<'WRAP'
#!/bin/bash
set -e
exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f /workspace/solidity-lean/.diagnostic-lakefile.toml "$@"
WRAP
chmod +x "$repo/.lake/diagnostic-tools/lake"
cat > "$output/ReaderPreflight.lean" <<'LEAN'
import Solidity.Frontend.SolcJson.Contract
#check Solidity.Frontend.Source.read
#check Solidity.Frontend.readContract
#check Solidity.Frontend.Admission.scan
LEAN
name="solidity-baseline-reader-repro-$$"
managed_docker() { env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH docker --host=unix:///var/run/docker.sock "$@"; }
cleanup() {
 local state
 state=$(managed_docker inspect "$name" --format '{{.State.Running}}') || { echo 'Container state unknown: preserve session config'; return 1; }
 if [[ "$state" = true ]]; then managed_docker stop -t 10 "$name" >/dev/null || return 1; fi
 [[ "$(managed_docker inspect "$name" --format '{{.State.Running}}')" = false ]] || return 1
 rm "$config"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
managed_docker run --name "$name" --network none --memory 12g --memory-swap 12g --cpus 1 --user "$(id -u):$(id -g)" \
 -v /workspace:/workspace -v /opt:/opt:ro -v /usr:/usr:ro -v /lib:/lib:ro -v /lib64:/lib64:ro -v /bin:/bin:ro \
 -w "$repo" ubuntu@sha256:24737cef17f4e22b1977df7d9a05e77c4e28b7da5b8911f8d8ccda136bf3573c /bin/bash -c '
set -euo pipefail
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/usr/bin:/bin
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 BASELINE_READER_ONLY=1 BASELINE_PROBE_OUT="$1"
export PATH=/workspace/solidity-lean/.lake/diagnostic-tools:$PATH
python3 scripts/solidity-baseline-time.py "$1/logs/reader-preflight" timeout -k 10 120 lake --quiet --no-build lean "$1/ReaderPreflight.lean" -- --tstack=131072 -j1
python3 scripts/solidity-baseline-time.py "$1/logs/diagnostics" timeout -k 10 600 node scripts/solidity-baseline-probe.mjs SourceIdentifiers CommentRanges VersionReject WrongIdentifier ConstantsEnums SourceTypes WrongNominal WrongBounds ScalarMatrixValid SourceLiterals WrongAddress InvalidDelete PushedMember TryContinue NominalStruct HexArray ExactRethrow WrongRethrow ComputedRevert SpecBindings BadClause HexArrayExplicit
python3 scripts/solidity-baseline-time.py "$1/logs/metadata" timeout -k 10 300 node scripts/solidity-baseline-reader-metadata.mjs
node scripts/solidity-baseline-probe-verify.mjs "$1"
' -- "$output"
