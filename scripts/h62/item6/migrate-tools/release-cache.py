#!/usr/bin/env python3
"""Release only this lane's off-Git file pages; do not delete artifacts.
Best-effort fadvise is not a claim of a fully cold OS/source cache.
Run with no Lean job, before both clean measurement attempts.
"""
import argparse, fcntl, json, os
from pathlib import Path
ap = argparse.ArgumentParser(); ap.add_argument("--output", type=Path, required=True)
args = ap.parse_args()
lock = open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a")
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
root = Path("/workspace/migrate-tools-evidence")
before = int(Path("/sys/fs/cgroup/memory.current").read_text())
files, size, errors = 0, 0, []
for path in sorted(root.rglob("*")):
    if path.is_symlink() or not path.is_file(): continue
    try:
        with path.open("rb") as stream:
            os.posix_fadvise(stream.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
        files += 1; size += path.stat().st_size
    except OSError as error: errors.append({"path": str(path), "error": str(error)})
after = int(Path("/sys/fs/cgroup/memory.current").read_text())
report = {"policy": "best-effort DONTNEED on lane-owned evidence files only; no content changes; not fully cold OS/source cache", "files": files, "bytes_advised": size, "cgroup_memory_before_bytes": before, "cgroup_memory_after_bytes": after, "errors": errors}
args.output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report))
