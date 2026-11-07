#!/usr/bin/env python3
"""Print a deterministic inventory of regular files in a diagnostic project."""
import argparse
import hashlib
import json
from pathlib import Path


def inventory(root: Path) -> dict:
    if root.is_symlink() or not root.is_dir():
        raise ValueError("project must be a real directory")
    files = []
    for path in sorted(root.rglob('*'), key=lambda p: p.relative_to(root).as_posix()):
        if path.is_symlink():
            raise ValueError(f"symlink in project: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise ValueError(f"non-regular file in project: {path}")
        before = path.stat()
        digest = hashlib.sha256()
        with path.open('rb') as source:
            for block in iter(lambda: source.read(1024 * 1024), b''):
                digest.update(block)
        after = path.stat()
        if (before.st_ino, before.st_size, before.st_mtime_ns) != (after.st_ino, after.st_size, after.st_mtime_ns):
            raise ValueError(f"file changed while reading: {path}")
        files.append({'path': path.relative_to(root).as_posix(), 'size': after.st_size, 'sha256': digest.hexdigest()})
    return {'files': files}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', type=Path)
    args = parser.parse_args()
    print(json.dumps(inventory(args.project), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
