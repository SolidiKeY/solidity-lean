#!/usr/bin/env python3
"""Compare archive member names with extracted toolchain paths, without writes."""
import pathlib
import subprocess

archive = "/workspace/lean-4.35.0-linux.tar.zst"
root = pathlib.Path("/workspace/h62-toolchain/lean-4.35.0-linux")
lines = subprocess.check_output(["tar", "--list", "--zstd", "-f", archive], text=True).splitlines()
prefix = "lean-4.35.0-linux/"
expected = set()
for line in lines:
    line = line.rstrip("/")
    if line == "lean-4.35.0-linux":
        continue
    if not line.startswith(prefix):
        raise SystemExit(f"unexpected archive prefix: {line}")
    relative = pathlib.PurePosixPath(line[len(prefix):])
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit(f"unsafe archive path: {relative}")
    expected.add(relative.as_posix())
    for parent in relative.parents:
        if str(parent) != ".":
            expected.add(parent.as_posix())
actual = {path.relative_to(root).as_posix() for path in root.rglob("*")}
missing, extra = sorted(expected-actual), sorted(actual-expected)
if missing or extra:
    raise SystemExit(f"toolchain layout differs: missing={missing[:20]}, extra={extra[:20]}")
print(f"archive/extraction path sets match: {len(expected)} entries")
