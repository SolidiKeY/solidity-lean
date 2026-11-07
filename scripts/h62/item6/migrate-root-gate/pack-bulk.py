#!/usr/bin/env python3
"""Deterministically pack H44 intake/evidence data from an exact held Git snapshot.

Guarded regression: moving data off Git must preserve every selected byte and
must not turn recovered metadata into historical compiler-export acceptance.
Usage: pack-bulk.py SOURCE_COMMIT BASE_COMMIT FRESH_ARCHIVE_PATH
The archive is external; only its path/size/SHA256 manifest belongs in Git.
"""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[4]


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def bulk_path(path):
    if path.startswith("tests/h62/item6/"):
        return ("/handoff/" in path or "/retirement/" in path or
                Path(path).suffix in (".json", ".txt", ".xml") or
                Path(path).name == "SHA256SUMS")
    return (path.startswith("scripts/h62/item6/migrate-root-gate/") and
            path.endswith(".json") and not path.endswith("/bulk-manifest.json"))


def pack(source, base, output):
    source = git("rev-parse", "--verify", source+"^{commit}").decode().strip()
    base = git("rev-parse", "--verify", base+"^{commit}").decode().strip()
    paths = sorted(p for p in git("diff", "--name-only", "--diff-filter=A", base, source,
                                 "--", "tests/h62/item6", "scripts/h62/item6").decode().splitlines()
                   if bulk_path(p))
    if not paths:
        raise ValueError("No selected H44 bulk inputs")
    total = 0
    with output.open("xb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0, compresslevel=9) as compressed:
            with tarfile.open(fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT) as archive:
                for path in paths:
                    data = git("show", source+":"+path)
                    info = tarfile.TarInfo(path)
                    info.size = len(data); info.mode = 0o644; info.mtime = 0
                    archive.addfile(info, io.BytesIO(data)); total += len(data)
    data = output.read_bytes()
    return {"schema_version": 1, "archive": str(output.resolve()), "size_bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest(), "file_count": len(paths),
            "uncompressed_bytes": total, "held_source_head": source, "source_base": base,
            "boundary": "H44 archival split of existing tracked evidence/intake bytes only; not recovery or acceptance of missing historical compiler exports."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source"); parser.add_argument("base"); parser.add_argument("output", type=Path)
    args = parser.parse_args()
    print(json.dumps(pack(args.source, args.base, args.output), indent=2))
