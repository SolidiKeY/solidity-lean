#!/usr/bin/env python3
"""Bounded, non-extracting draft packet intake. Never a kernel evidence validator."""
import argparse
import zlib
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import resource
import signal
import tarfile

COMPRESSED = 16 * 1024**2
RAW = 32 * 1024**2
SHA = re.compile(r"[0-9a-f]{64}")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def object_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def load(data):
    return json.loads(data, object_pairs_hook=object_pairs)


def safe_path(name):
    p = PurePosixPath(name)
    require(isinstance(name, str) and bool(name) and not p.is_absolute()
            and name != "." and len(name) <= 4096 and str(p) == name and ".." not in p.parts
            and all(ord(c) >= 32 and ord(c) != 127 for c in name)
            and "\\" not in name and ".git" not in p.parts, "unsafe packet path")
    return name


def stable_read(path, limit):
    path = Path(path)
    require(not path.is_symlink(), "symlink input")
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK), "rb") as f:
        import stat
        before = os.fstat(f.fileno())
        require(stat.S_ISREG(before.st_mode), "nonregular input")
        require(before.st_size <= limit, "input size bound")
        data = f.read(limit + 1)
        after = os.fstat(f.fileno())
    fields = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
    require(fields(before) == fields(after) and len(data) == before.st_size,
            "input changed/truncated")
    require(len(data) <= limit, "input size bound")
    return data


def _inspect(packet, expected):
    # expected is an independently relayed allowlist, never a manifest trusted from the archive.
    require(isinstance(expected, dict) and set(expected) == {"schema", "packetSha256", "producerHead", "members"},
            "unsupported request shape")
    require(type(expected["schema"]) is int and expected["schema"] == 1, "request schema")
    require(isinstance(expected["producerHead"], str) and
            re.fullmatch(r"[0-9a-f]{40}", expected["producerHead"]), "producer head")
    require(isinstance(expected["packetSha256"], str) and SHA.fullmatch(expected["packetSha256"]),
            "packet digest shape")
    members = expected["members"]
    require(isinstance(members, dict) and 0 < len(members) <= 256, "member allowlist")
    for name, digest in members.items():
        safe_path(name)
        require(isinstance(digest, str) and SHA.fullmatch(digest), "member digest shape")
    require(len(packet) <= COMPRESSED, "compressed bound")
    require(hashlib.sha256(packet).hexdigest() == expected["packetSha256"], "packet digest mismatch")
    decoder = zlib.decompressobj(16 + zlib.MAX_WBITS)
    raw = decoder.decompress(packet, RAW + 1)
    require(len(raw) <= RAW, "raw bound")
    require(decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail,
            "truncated or concatenated gzip stream")
    # Require canonical zero termination, including padding; tarfile alone accepts truncation.
    require(len(raw) % 512 == 0 and raw.endswith(bytes(1024)), "incomplete tar termination")
    actual = {}
    bodies = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode="r:") as archive:
        for item in archive:
            safe_path(item.name)
            require(item.offset_data == item.offset + 512, "extended tar header")
            require(item.name not in actual, "duplicate member")
            require(item.isfile() and not item.issparse() and not item.pax_headers
                    and item.type in (tarfile.REGTYPE, tarfile.AREGTYPE), "unsupported member")
            require(item.name in members, "unexpected member")
            require(0 <= item.size <= RAW, "member size bound")
            body = archive.extractfile(item).read(item.size + 1)
            require(len(body) == item.size, "truncated member")
            bodies[item.name] = body
            actual[item.name] = hashlib.sha256(body).hexdigest()
            require(actual[item.name] == members[item.name], "member digest mismatch")
        end = archive.offset
    require(len(raw) - end >= 1024, "missing end blocks")
    require(not any(raw[end:]), "trailing archive data")
    require(actual == members, "missing members")
    return {"schema": 1, "status": "source-bytes-only", "producerHeadClaim": expected["producerHead"],
            "packetSha256": expected["packetSha256"], "members": actual,
            "compressedBytes": len(packet), "rawBytes": len(raw),
            "kernelValidated": False, "replayValidated": False,
            "semanticPremisesDischarged": False, "releaseClosed": False,
            "pending": ["committed anchor identity", "complete dependency/source inventory",
                        "full declaration extraction", "mandatory live replay",
                        "axiom/type/observation result linkage"]}, bodies


def inspect(packet, expected):
    return _inspect(packet, expected)[0]

def main():
    resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2, 512 * 1024**2))
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError("metadata deadline")))
    signal.alarm(60)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packet", type=Path)
    parser.add_argument("expected", type=Path)
    args = parser.parse_args()
    try:
        result = inspect(stable_read(args.packet, COMPRESSED), load(stable_read(args.expected, 1024**2)))
        print(json.dumps(result, sort_keys=True))
    except (TypeError, ValueError, OSError, EOFError, tarfile.TarError, zlib.error, TimeoutError, MemoryError) as exc:
        print(json.dumps({"status": "NONPASS", "error": str(exc), "kernelValidated": False,
                          "releaseClosed": False, "semanticPremisesDischarged": False}))
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
