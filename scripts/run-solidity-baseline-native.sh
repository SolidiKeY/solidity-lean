#!/usr/bin/env bash
# No build/config edits. Validate existing artifacts before production native IO.
set -euo pipefail
repo=$(realpath "$(git rev-parse --show-toplevel)")
[[ "$repo" = /workspace/solidity-lean && $# = 1 ]] || { echo 'usage from attached clone: scripts/run-solidity-baseline-native.sh FRESH_OUTPUT'; exit 2; }
cd "$repo"
out=$(realpath -m "$1")
[[ "$out" = "$repo/"* && ! -e "$out" ]] || { echo 'fresh output under attached clone required'; exit 2; }
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
git status --short
git diff --exit-code c4a5a2f1 -- Solidity Solidity.lean lakefile.toml scripts/solc-ast.mjs scripts/solc-code.mjs scripts/solidity-upstream.mjs >/dev/null
[[ -z "$(git ls-files --others --exclude-standard -- Solidity | rg '\.lean$')" ]] || exit 2
mkdir -p "$out/inputs" "$out/logs"
python3 - "$out" <<'INPUTS'
from pathlib import Path
import sys,json,tarfile,hashlib
src=Path('tests/upstream/baseline-20261028/native-cache');ledger=json.loads((src/'archive.json').read_text());archive=src/'evidence.tar.gz';assert hashlib.sha256(archive.read_bytes()).hexdigest()==ledger['sha256']
out=Path(sys.argv[1])
with tarfile.open(archive,'r:gz') as tf:
 for member in tf:
  parts=Path(member.name).parts
  if member.isfile() and len(parts)==4 and parts[0]=='run-inputs' and parts[2]=='legacy' and parts[3]=='source.sol':
   data=tf.extractfile(member).read();assert hashlib.sha256(data).hexdigest()==ledger['files'][member.name]['sha256'];(out/'inputs'/(parts[1]+'.sol')).write_bytes(data)
 for name in ['FileHashes.lean','NativePreflight.lean']:
  data=tf.extractfile(name).read();assert hashlib.sha256(data).hexdigest()==ledger['files'][name]['sha256'];(out/name).write_bytes(data)
INPUTS
name="solidity-baseline-native-repro-$$"
managed_docker() { env -u DOCKER_HOST -u DOCKER_CONTEXT -u DOCKER_TLS -u DOCKER_TLS_VERIFY -u DOCKER_CERT_PATH docker --host=unix:///var/run/docker.sock "$@"; }
cleanup() {
 local state
 state=$(managed_docker inspect "$name" --format '{{.State.Running}}') || { echo 'Unknown container state: preserve outputs for recovery'; return 1; }
 if [[ "$state" = true ]]; then managed_docker stop -t 10 "$name" >/dev/null; fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
managed_docker run --name "$name" --network none --memory 12g --memory-swap 12g --cpus 1 --user "$(id -u):$(id -g)" \
 -v /workspace:/workspace -v /opt:/opt:ro -v /usr:/usr:ro -v /lib:/lib:ro -v /lib64:/lib64:ro -v /bin:/bin:ro -w "$repo" \
 ubuntu@sha256:24737cef17f4e22b1977df7d9a05e77c4e28b7da5b8911f8d8ccda136bf3573c /bin/bash -c '
set -euo pipefail
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:/usr/bin:/bin
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 BASELINE_NATIVE_OUT="$1"
python3 scripts/solidity-baseline-cache-audit.py --out "$1"
python3 scripts/solidity-baseline-time.py "$1/logs/file-hashes" timeout -k 10 120 lean -j1 --run "$1/FileHashes.lean" "$1/hash-jobs.json" "$1/file-hashes.json"
python3 scripts/solidity-baseline-cache-audit.py --out "$1" --hashes "$1/file-hashes.json"
python3 scripts/solidity-baseline-time.py "$1/logs/native-preflight" timeout -k 10 120 lake --quiet --no-build lean "$1/NativePreflight.lean" -- --tstack=131072 -j1
python3 scripts/solidity-baseline-time.py "$1/logs/native-checks" timeout -k 10 600 node scripts/solidity-baseline-native.mjs NativePositive SourceIdentifiers CommentRanges ConstantsEnums SourceTypes BadClause CommentSpecPositive ScalarMatrixValid SourceLiterals NominalStruct PushedMember PushedMemberPositive TryContinue TryContinuePositive HexArrayExplicit ExactRethrow WrongRethrow ComputedRevert SpecBindings PushedMemberMutation
python3 scripts/solidity-baseline-time.py "$1/logs/native-boundaries" timeout -k 10 120 node scripts/solidity-baseline-native-boundaries.mjs
node scripts/solidity-baseline-native-verify.mjs "$1"
' -- "$out"
