#!/usr/bin/env bash
# Conditional consumer probe on a published Hash overlay, never a runtime gate.
set -euo pipefail
[[ $# == 0 ]] || { echo "usage: $0" >&2; exit 2; }
root="$(cd "$(dirname "$0")/../../../.." && pwd)"
exec flock -x /tmp/solidity-lean-feature-groups-20261025/writer.lock bash -c '
  set -euo pipefail
  cd "$1"
  overlay=/workspace/h62-packet-panic-overlay-2a18-snapshot-v1
  archive=/workspace/h62-packet-panic-postmerge-evidence/overlay-2a18-probe-v1.tar
  commit=2a18afcdba00a85645b0b3079704f78ffcd78860
  helper=Solidity/Backend/PrimitivePackets/PanicBytes.lean
  expected=c1d3eeb8f7c23308ee1b0b33fb7be331e7792f7bf8e646812517453db7428246
  [[ ! -e "$overlay" && ! -L "$overlay" && ! -e "$archive" && ! -L "$archive" ]] || { echo "snapshot or archive path exists; preserve it and stop" >&2; exit 1; }
  [[ -z "$(git status --porcelain)" ]] || { echo "assigned checkout is dirty; stop" >&2; exit 1; }
  git merge-base --is-ancestor c6f550e281a7e5affa9a99bc2cdaed556dec00e4 "$commit"
  [[ "$(sha256sum "$helper" | cut -d " " -f1)" == "$expected" ]] || { echo "registered helper digest changed" >&2; exit 1; }
  flock -n /tmp/solidity-lean-feature-groups-20261025/lean-serial.lock true || { echo "serial Lean lock is held" >&2; exit 1; }
  PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/packet-panic/prepare_serial_toolchain.py
  PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/packet-panic/verify_toolchain_layout.py
  compare=/workspace/h62-packet-panic-postmerge-evidence/overlay-toolchain-archive-compare.log
  rc=0
  tar --compare --zstd -f /workspace/lean-4.35.0-linux.tar.zst -C /workspace/h62-toolchain > "$compare" 2>&1 || rc=$?
  if (( rc > 1 )) || rg -q -v ": (Mode|Uid|Gid) differs$" "$compare"; then
    echo "official archive comparison reported non-metadata differences" >&2
    exit 1
  fi
  echo "archive comparison: no differences other than recorded mode/uid/gid"
  PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item1/packet-panic/materialize_overlay_snapshot.py --repository "$PWD" --commit "$commit" --archive "$archive" --destination "$overlay"
  [[ ! -e "$overlay/.git" && ! -L "$overlay/.git" ]] || { echo "snapshot unexpectedly contains Git metadata" >&2; exit 1; }
  lane=tests/h62/item1/packet-panic
  project="$overlay/$lane/closure-project-overlay"
  mkdir -p "$project"
  cp "$helper" "$project/PanicBytes.lean"
  cmp "$helper" "$project/PanicBytes.lean"
  cp "$lane/closure-project-overlay/lakefile.toml" "$project/lakefile.toml"
  cp "$lane/closure-project-overlay/lean-toolchain" "$project/lean-toolchain"
  cp "$lane/closure-project-overlay/.gitignore" "$project/.gitignore"
  echo "overlay commit: $commit"
  echo "registered helper sha256: $expected"
  sha256sum "$overlay/Solidity/Hash/CollisionBound.lean" "$overlay/Solidity/Hash/Adaptive.lean" "$overlay/Solidity/Source/Observe.lean" "$overlay/Solidity/Source/Types.lean"
  echo "unregistered source snapshot: $overlay"
  echo "preserved source archive: $archive"
  /workspace/h62-toolchain/lean-4.35.0-linux/bin/lean --version
  /workspace/h62-toolchain/lean-4.35.0-linux/bin/lake --version
  exec /workspace/solidity-lean/.venv/bin/python scripts/h62/item1/packet-panic/mcp_serial_diagnostic.py --project "$project" --diagnostic "$project/PanicBytes.lean"
' _ "$root"
