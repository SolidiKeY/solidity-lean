#!/usr/bin/env python3
"""Create an off-Git symlink view of the official toolchain with a serial Lean launcher."""
import hashlib
import os
from pathlib import Path

archive = Path("/workspace/lean-4.35.0-linux.tar.zst")
source = Path("/workspace/h62-toolchain/lean-4.35.0-linux")
destination = Path("/workspace/h62-packet-panic-postmerge-evidence/serial-toolchain")
expected = "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d"
h = hashlib.sha256()
with archive.open("rb") as stream:
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        h.update(block)
if h.hexdigest() != expected:
    raise SystemExit("official archive hash mismatch")
destination.mkdir(parents=True, exist_ok=True)
bin_dir = destination / "bin"
bin_dir.mkdir(exist_ok=True)
for path in source.iterdir():
    if path.name == "bin":
        continue
    link = destination / path.name
    if not link.exists() and not link.is_symlink():
        link.symlink_to(path, target_is_directory=path.is_dir())
    elif not link.is_symlink() or link.resolve() != path.resolve():
        raise SystemExit(f"unexpected existing toolchain entry: {link}")
for path in (source / "bin").iterdir():
    if path.name == "lean":
        continue
    link = bin_dir / path.name
    if not link.exists() and not link.is_symlink():
        link.symlink_to(path)
    elif not link.is_symlink() or link.resolve() != path.resolve():
        raise SystemExit(f"unexpected existing toolchain binary: {link}")
wrapper = bin_dir / "lean"
body = """#!/usr/bin/env bash
set -euo pipefail
real=/workspace/h62-toolchain/lean-4.35.0-linux/bin/lean
for arg in "$@"; do
  if [[ "$arg" == --server || "$arg" == --version || "$arg" == --print-prefix ]]; then
    exec "$real" -j1 "$@"
  fi
done
exec flock -x /tmp/solidity-lean-feature-groups-20261025/lean-serial.lock "$real" -j1 "$@"
"""
if wrapper.exists() and (wrapper.is_symlink() or wrapper.read_text() != body):
    raise SystemExit(f"unexpected existing Lean launcher: {wrapper}")
wrapper.write_text(body)
os.chmod(wrapper, 0o755)
print(f"official archive SHA-256 {h.hexdigest()}; symlink view {destination}")
