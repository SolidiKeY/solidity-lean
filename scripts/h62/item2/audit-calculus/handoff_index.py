"""Guard against truncated handoff receipt claims; byte checks are not proof validation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re

REQUIRED = {"HANDOFF.md", "gates.json", "evidence.tar.gz", "original.patch"}


def fingerprint(stat):
    return (stat.st_dev, stat.st_ino, stat.st_mode, stat.st_size,
            stat.st_mtime_ns, stat.st_ctime_ns)


def checked_read(path, limit=None):
    """Bind a streamed hash/size to one stable, nonsymlink file version."""
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(descriptor, "rb") as stream:
        before = os.fstat(stream.fileno())
        if fingerprint(before) != fingerprint(path.stat(follow_symlinks=False)):
            raise ValueError("artifact identity changed: " + path.name)
        if limit is not None and before.st_size > limit:
            raise ValueError("checksum manifest exceeds receipt bound")
        digest = hashlib.sha256()
        captured = bytearray() if limit is not None else None
        count = 0
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            count += len(chunk)
            if limit is not None and count > limit:
                raise ValueError("checksum manifest exceeds receipt bound")
            digest.update(chunk)
            if captured is not None:
                captured.extend(chunk)
        after = os.fstat(stream.fileno())
        if (fingerprint(before) != fingerprint(after)
                or fingerprint(after) != fingerprint(path.stat(follow_symlinks=False))
                or count != after.st_size):
            raise ValueError("artifact changed while reading: " + path.name)
    return digest.hexdigest(), count, bytes(captured) if captured is not None else None


def build_index(root):
    """Verify every flat SHA256SUMS entry; emit only a bounded summary."""
    root = Path(root).resolve(strict=True)
    manifest = root / "SHA256SUMS"
    if manifest.is_symlink() or not manifest.is_file():
        raise ValueError("missing or symlinked checksum manifest")
    manifest_hash, manifest_size, manifest_bytes = checked_read(manifest, 32768)
    entries = {}
    for line in manifest_bytes.decode("utf-8").splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  ([A-Za-z0-9][A-Za-z0-9_.-]{0,127})", line)
        if not match:
            raise ValueError("malformed or non-flat checksum entry")
        expected, name = match.groups()
        if name in entries or name == "SHA256SUMS":
            raise ValueError("duplicate or self-referential checksum entry")
        path = root / name
        if path.is_symlink() or not path.is_file():
            raise ValueError("missing or symlinked handoff artifact: " + name)
        actual, size, _ = checked_read(path)
        if actual != expected:
            raise ValueError("checksum mismatch: " + name)
        entries[name] = {"path": str(path), "bytes": size, "sha256": expected}
        if len(entries) > 64:
            raise ValueError("too many handoff entries")
    if not REQUIRED <= entries.keys():
        raise ValueError("required handoff artifacts absent")
    if checked_read(manifest, 32768) != (manifest_hash, manifest_size, manifest_bytes):
        raise ValueError("checksum manifest changed during verification")
    return {
        "schema_version": 1,
        "kind": "local-handoff-byte-receipt",
        "manifest": {"path": str(manifest), "bytes": manifest_size,
                     "sha256": manifest_hash},
        "verified_entries": len(entries),
        "selected_artifacts": {name: entries[name] for name in sorted(REQUIRED)},
        "boundary": "Local manifest/artifact bytes verified only; no coordinator retrieval, "
                    "census completeness, semantic, Lean, axiom or runtime acceptance inferred.",
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    args = parser.parse_args(argv)
    try:
        result = build_index(args.root)
    except (ValueError, OSError, UnicodeError) as error:
        parser.exit(1, "handoff byte check failed: " + str(error) + "\n")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
