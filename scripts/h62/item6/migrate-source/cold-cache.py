#!/usr/bin/env python3
"""Evict only task-private toolchain/build clean pages before either measurement.
Does not alter file contents, kernel limits, global caches, or other workers.
Arguments must be the same directory roots for both measurements.
"""
import os
from pathlib import Path
import sys
count=0
for arg in sys.argv[1:]:
    root=Path(arg).resolve()
    if not (root.is_relative_to(Path("/workspace/h62-migrate-source-evidence")) or str(root)=="/workspace/.setup/tools/lean-4.24.0-linux"):
        raise SystemExit("unowned cache root refused: "+str(root))
    for path in root.rglob("*"):
        if path.is_file() and not path.is_symlink():
            with path.open("rb") as f:
                os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)
            count+=1
print("Advised eviction of clean pages for",count,"task-private files; no files changed")
