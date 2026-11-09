#!/usr/bin/env python3
"""Guard H127 offline lifecycle intake against substituted or truncated records.

An externally pinned canonical journal is structurally inspected without opening
its live store, acquiring its lease, executing facts, or changing a barrier.
SHA256/chain validity is not hostile-writer authentication or fact verification.
Every cleanup/resource/measurement acceptance field remains false.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import stat

_spec = importlib.util.spec_from_file_location("h127_offline_journal", Path(__file__).with_name("lifecycle-journal.py"))
journal = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(journal)
LIMIT = 65536


def fingerprint(s):
    return (s.st_dev, s.st_ino, s.st_mode, s.st_uid, s.st_gid,
            s.st_nlink, s.st_size, s.st_mtime_ns, s.st_ctime_ns)


def read_pinned(path, expected):
    """Read one bounded, unaliased regular file via nofollow ancestor FDs."""
    if not isinstance(expected, str) or not journal.HEX64.fullmatch(expected):
        raise ValueError("external SHA256 pin required")
    raw = os.fspath(path)
    if not raw.startswith("/") or any(p in (".", "..") for p in raw.split("/")):
        raise ValueError("absolute path without dot components required")
    parts = Path(raw).parts[1:]
    if not parts:
        raise ValueError("regular journal file required")
    parent = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    fd = None
    try:
        for part in parts[:-1]:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent)
            os.close(parent)
            parent = child
        fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent)
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1 or before.st_size > LIMIT:
            raise ValueError("bounded unaliased regular journal required")
        data = bytearray()
        while len(data) <= LIMIT:
            block = os.read(fd, min(4096, LIMIT + 1 - len(data)))
            if not block:
                break
            data.extend(block)
        after = os.fstat(fd)
        entry = os.stat(parts[-1], dir_fd=parent, follow_symlinks=False)
        if (len(data) > LIMIT or len(data) != before.st_size or
                fingerprint(before) != fingerprint(after) or fingerprint(after) != fingerprint(entry)):
            raise ValueError("journal changed during bounded read")
        if hashlib.sha256(data).hexdigest() != expected:
            raise ValueError("journal SHA256 differs from external pin")
        return bytes(data)
    finally:
        if fd is not None:
            os.close(fd)
        os.close(parent)


def inspect_bytes(data, expected):
    if not isinstance(expected, str) or not journal.HEX64.fullmatch(expected):
        raise ValueError("external SHA256 pin required")
    if type(data) is not bytes or len(data) > LIMIT:
        raise ValueError("bounded journal bytes required")
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError("journal SHA256 differs from external pin")
    value = json.loads(data)
    if not isinstance(value, dict) or journal.encode(value) != data:
        raise ValueError("canonical journal required")
    journal.Journal._validate(value)
    return {"schemaVersion": 1, "journalSha256": expected,
            "identity": value["identity"], "eventCount": len(value["events"]),
            "lastRecordedState": value["events"][-1]["state"],
            "lastEventSha256": journal.digest(value["events"][-1]),
            "structureValid": True, "recordedFactsVerified": False,
            "liveLeaseAuthenticated": False, "cleanupAccepted": False,
            "resourceAccepted": False, "measurementAccepted": False,
            "postCreateBarrierReleased": False,
            "boundary": "Pinned record structure only; no live-store, kernel, Docker, source, resource or measurement verification."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path")
    parser.add_argument("--sha256", required=True)
    args = parser.parse_args()
    result = inspect_bytes(read_pinned(args.path, args.sha256), args.sha256)
    print(json.dumps(result, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
