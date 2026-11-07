#!/usr/bin/env python3
"""Guard regression: H109 cache copies differ without an observed stop.

A static comparison, not an atomic snapshot or provenance attestation. Caller
must hold the repository writer lock and prevent other cache writers.
"""
import hashlib
import json
import os
import pathlib
import stat
import sys

RESERVE = 4 * 1024 ** 3


def headroom():
    base = pathlib.Path("/sys/fs/cgroup")
    cap = int((base / "memory.max").read_text().strip())
    used = int((base / "memory.current").read_text().strip())
    swap = int((base / "memory.swap.current").read_text().strip())
    fields = {line.split(":", 1)[0]: line.split(":", 1)[1].strip() for line in pathlib.Path("/proc/meminfo").read_text().splitlines() if ":" in line}
    available = int(fields["MemAvailable"].split()[0]) * 1024
    swap_total = int(fields["SwapTotal"].split()[0])
    if used > cap or cap - used < RESERVE or available < RESERVE or swap or swap_total:
        raise ValueError("resource stop: reserve or no-swap condition")


def identity(info):
    return info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns


def snapshot(root, check=headroom):
    root = pathlib.Path(root)
    if not root.is_absolute() or root.resolve() != root or not root.is_dir():
        raise ValueError("cache root must be canonical absolute directory")
    rows, inodes = [], set()
    def walk(directory):
        check()
        initial = directory.stat(follow_symlinks=False)
        if not stat.S_ISDIR(initial.st_mode):
            raise ValueError("non-directory cache root")
        inodes.add((initial.st_dev, initial.st_ino))
        rows.append([directory.relative_to(root).as_posix(), "dir", stat.S_IMODE(initial.st_mode), initial.st_uid, initial.st_gid, initial.st_mtime_ns])
        with os.scandir(directory) as entries:
            names = sorted(e.name for e in entries)
        for name in names:
            path = directory / name
            entry = path.stat(follow_symlinks=False)
            if stat.S_ISDIR(entry.st_mode):
                walk(path)
            elif stat.S_ISREG(entry.st_mode):
                fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK)
                try:
                    opened = os.fstat(fd)
                    if identity(opened) != identity(entry):
                        raise ValueError("cache file replaced")
                    digest = hashlib.sha256()
                    while True:
                        check()
                        chunk = os.read(fd, 1024 * 1024)
                        if not chunk:
                            break
                        digest.update(chunk)
                    if identity(opened) != identity(os.fstat(fd)) or identity(opened) != identity(path.stat(follow_symlinks=False)):
                        raise ValueError("cache file changed")
                    os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)
                finally:
                    os.close(fd)
                inodes.add((opened.st_dev, opened.st_ino))
                rows.append([path.relative_to(root).as_posix(), "file", stat.S_IMODE(opened.st_mode),
                             opened.st_uid, opened.st_gid, opened.st_nlink, opened.st_size, opened.st_mtime_ns, digest.hexdigest()])
            else:
                raise ValueError("symlink or special cache entry")
        if identity(initial) != identity(directory.stat(follow_symlinks=False)):
            raise ValueError("cache directory changed")
    walk(root)
    return rows, inodes


def compare(before, after, check=headroom):
    left, right = pathlib.Path(before), pathlib.Path(after)
    if (not left.is_absolute() or not right.is_absolute() or left.resolve() != left or right.resolve() != right
            or left == right or left.is_relative_to(right) or right.is_relative_to(left)):
        raise ValueError("cache roots must be distinct, canonical and nonoverlapping")
    a, ai = snapshot(left, check)
    b, bi = snapshot(right, check)
    if ai & bi:
        raise ValueError("cache copies share filesystem inodes")
    digest = lambda rows: hashlib.sha256(json.dumps(rows, ensure_ascii=True, separators=(",", ":")).encode()).hexdigest()
    return {"status": "equal-observation" if a == b else "different-observation", "entries": [len(a), len(b)],
            "manifest_sha256": [digest(a), digest(b)],
            "limitation": "non-atomic selected metadata; ACLs, xattrs, backing storage, page-cache state and provenance are unverified"}


def main():
    if len(sys.argv) != 3:
        print("usage: h109_cache_compare.py BEFORE AFTER", file=sys.stderr)
        return 2
    try:
        result = compare(sys.argv[1], sys.argv[2])
        print(json.dumps(result, indent=2))
        return 0 if result["status"] == "equal-observation" else 1
    except (OSError, ValueError, KeyError) as exc:
        print(f"cache comparison unavailable: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
