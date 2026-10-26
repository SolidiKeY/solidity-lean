#!/usr/bin/env python3
"""Recreate the complete pinned upstream test tree and its license, unchanged."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

PIN = "1835d247de183f23e7b0e2bc4a50732af525b77c"
SUBMODULE = "test/ethdebugSchemaTests/ethdebug-format"
SUBMODULE_PIN = "937e3484cb4cf408a4e808d62f34285a71fece80"


def snapshot(checkout: Path, destination: Path) -> dict:
    commit = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "v0.8.38^{commit}"], text=True
    ).strip()
    if commit != PIN:
        raise ValueError("v0.8.38 differs from this repository's language inventory pin")
    raw = subprocess.check_output(
        ["git", "-C", str(checkout), "archive", "--format=tar", PIN, "test", "LICENSE.txt"]
    )
    submodule_commit = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", f"{PIN}:{SUBMODULE}"], text=True
    ).strip()
    if submodule_commit != SUBMODULE_PIN:
        raise ValueError("unexpected schema submodule pin")
    submodule_bytes = subprocess.check_output(
        ["git", "-C", str(checkout / SUBMODULE), "archive", "--format=tar", SUBMODULE_PIN]
    )
    merged = io.BytesIO()
    with tarfile.open(fileobj=merged, mode="w") as output:
        for content, prefix in [(raw, ""), (submodule_bytes, SUBMODULE + "/")]:
            with tarfile.open(fileobj=io.BytesIO(content)) as archive:
                for entry in archive:
                    entry.name = prefix + entry.name
                    output.addfile(entry, archive.extractfile(entry) if entry.isfile() else None)
    raw = merged.getvalue()
    files = []
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        for entry in archive:
            if entry.isdir():
                continue
            if not entry.isfile():
                raise ValueError(f"unexpected non-regular archive entry: {entry.name}")
            content = archive.extractfile(entry).read()
            files.append({"path": entry.name, "bytes": len(content),
                          "sha256": hashlib.sha256(content).hexdigest()})
    destination.mkdir(parents=True, exist_ok=True)
    archive = destination / "solidity-0.8.38.tar.gz"
    archive.write_bytes(gzip.compress(raw, mtime=0))
    manifest = {
        "version": 1, "repository": "https://github.com/argotorg/solidity",
        "tag": "v0.8.38", "commit": PIN, "archive": archive.name,
        "submodules": [{"path": SUBMODULE, "repository": "https://github.com/ethdebug/format",
                        "commit": SUBMODULE_PIN}],
        "archiveSha256": hashlib.sha256(archive.read_bytes()).hexdigest(), "files": files,
    }
    (destination / "snapshot.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).resolve().parents[1] / "tests/upstream")
    args = parser.parse_args()
    manifest = snapshot(args.checkout, args.out)
    print(f"Snapshotted {len(manifest['files'])} files at {manifest['commit']}")
