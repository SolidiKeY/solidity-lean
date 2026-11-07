#!/usr/bin/env python3
"""Fingerprint an explicit cache tree; does not authenticate its origin."""
import hashlib
import json
import os
import pathlib
import stat


def identity(info):
    return info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns


def fingerprint(root):
    root = pathlib.Path(root)
    if not root.is_absolute() or root.is_symlink() or not root.is_dir() or root.resolve() != root:
        raise ValueError("cache root must be an absolute non-symlink directory")
    rows, directories = [], []
    def walk(directory):
        before = directory.stat(follow_symlinks=False)
        if not stat.S_ISDIR(before.st_mode):
            raise ValueError("cache directory changed")
        with os.scandir(directory) as iterator:
            names = sorted(entry.name for entry in iterator)
        for name in names:
            path = directory / name
            expected = path.stat(follow_symlinks=False)
            if stat.S_ISLNK(expected.st_mode):
                raise ValueError("cache symlink rejected")
            if stat.S_ISDIR(expected.st_mode):
                directories.append({"path": path.relative_to(root).as_posix(), "mode": stat.S_IMODE(expected.st_mode), "mtime_ns": expected.st_mtime_ns})
                walk(path)
                if identity(expected) != identity(path.stat(follow_symlinks=False)):
                    raise ValueError("cache directory changed")
                continue
            if not stat.S_ISREG(expected.st_mode):
                raise ValueError("nonregular cache file")
            fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK)
            try:
                opened = os.fstat(fd)
                if identity(expected) != identity(opened) or not stat.S_ISREG(opened.st_mode):
                    raise ValueError("cache file replaced")
                h = hashlib.sha256()
                while True:
                    chunk = os.read(fd, 1024 * 1024)
                    if not chunk:
                        break
                    h.update(chunk)
                if identity(opened) != identity(os.fstat(fd)) or identity(opened) != identity(path.stat(follow_symlinks=False)):
                    raise ValueError("cache file changed")
            finally:
                os.close(fd)
            rows.append({"path": path.relative_to(root).as_posix(), "size": opened.st_size,
                         "mode": stat.S_IMODE(opened.st_mode), "mtime_ns": opened.st_mtime_ns,
                         "links": opened.st_nlink, "sha256": h.hexdigest()})
        if identity(before) != identity(directory.stat(follow_symlinks=False)):
            raise ValueError("cache directory changed")
    root_info = root.stat(follow_symlinks=False)
    walk(root)
    if identity(root_info) != identity(root.stat(follow_symlinks=False)):
        raise ValueError("cache root changed")
    data = {"root_mode": stat.S_IMODE(root_info.st_mode), "root_mtime_ns": root_info.st_mtime_ns,
            "directories": directories, "files": rows}
    raw = json.dumps(data, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode()
    return {**data, "manifest_sha256": hashlib.sha256(raw).hexdigest()}
