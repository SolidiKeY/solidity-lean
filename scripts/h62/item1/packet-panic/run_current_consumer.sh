#!/usr/bin/env bash
# Fresh current-tree helper diagnostic; not a runtime or equivalence gate.
set -euo pipefail
[[ $# == 0 ]] || { echo "usage: $0" >&2; exit 2; }
root="$(cd "$(dirname "$0")/../../../.." && pwd)"
exec flock -x /tmp/solidity-lean-feature-groups-20261025/writer.lock bash -c '
  set -euo pipefail
  cd "$1"
  lane=tests/h62/item1/packet-panic
  project="$PWD/$lane/closure-project-current"
  helper=Solidity/Backend/PrimitivePackets/PanicBytes.lean
  expected=c1d3eeb8f7c23308ee1b0b33fb7be331e7792f7bf8e646812517453db7428246
  source_head=7de6f66ad29488d70e3c31c6b2a4798b72a0a209
  [[ -z "$(git status --porcelain)" ]] || { echo "assigned checkout is dirty; stop" >&2; exit 1; }
  [[ ! -e "$project/.lake" && ! -L "$project/.lake" && ! -e "$project/lake-manifest.json" && ! -L "$project/lake-manifest.json" && ! -e "$project/PanicBytes.lean" && ! -L "$project/PanicBytes.lean" ]] || { echo "current diagnostic artifacts exist; preserve them and stop" >&2; exit 1; }
  git merge-base --is-ancestor "$source_head" HEAD
  git diff --quiet "$source_head" HEAD -- Solidity
  [[ -z "$(git ls-files --others --ignored --exclude-standard -- ":(glob)Solidity/**/*.lean")" ]] || { echo "ignored Solidity source files exist; inspect and stop" >&2; exit 1; }
  [[ "$(sha256sum "$helper" | cut -d " " -f1)" == "$expected" ]] || { echo "registered helper digest changed" >&2; exit 1; }
  flock -n /tmp/solidity-lean-feature-groups-20261025/lean-serial.lock true || { echo "serial Lean lock is held" >&2; exit 1; }
  PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/packet-panic/prepare_serial_toolchain.py
  PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/packet-panic/verify_toolchain_layout.py
  compare=/workspace/h62-packet-panic-postmerge-evidence/current-toolchain-archive-compare.log
  [[ ! -e "$compare" && ! -L "$compare" ]] || { echo "toolchain comparison log exists; preserve it and stop" >&2; exit 1; }
  rc=0
  tar --compare --zstd -f /workspace/lean-4.35.0-linux.tar.zst -C /workspace/h62-toolchain > "$compare" 2>&1 || rc=$?
  if (( rc > 1 )) || rg -q -v ": (Mode|Uid|Gid) differs$" "$compare"; then
    echo "official archive comparison reported non-metadata differences" >&2
    exit 1
  fi
  echo "archive comparison: no differences other than recorded mode/uid/gid"
  cp --no-clobber "$helper" "$project/PanicBytes.lean"
  cmp "$helper" "$project/PanicBytes.lean"
  echo "current commit: $(git rev-parse HEAD)"
  echo "source baseline: $source_head"
  echo "registered helper sha256: $expected"
  sha256sum Solidity/Hash/CollisionBound.lean Solidity/Roadmap/Contracts.lean Solidity/Source/Observe.lean Solidity/Source/Types.lean
  /workspace/h62-toolchain/lean-4.35.0-linux/bin/lean --version
  /workspace/h62-toolchain/lean-4.35.0-linux/bin/lake --version
  exec /workspace/solidity-lean/.venv/bin/python scripts/h62/item1/packet-panic/mcp_serial_diagnostic.py --project "$project" --diagnostic "$project/PanicBytes.lean"
' _ "$root"
