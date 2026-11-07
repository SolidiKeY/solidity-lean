#!/usr/bin/env python3
"""Verify small committed input pins. Bulk census/output remains off git.
This checks source identity only; it does not certify Lean proofs or timings.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def verify(root, manifest):
    root = root.resolve()
    if manifest.get("schema_version") != 1 or not manifest.get("files"):
        raise ValueError("unsupported or empty manifest")
    seen = set()
    for entry in manifest["files"]:
        name = entry["path"]
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or name in seen or str(path) != name:
            raise ValueError("unsafe or duplicate repository-relative path: " + name)
        seen.add(name)
        target = (root/name).resolve()
        if not target.is_relative_to(root): raise ValueError("path escapes repository")
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        if actual != entry["sha256"]: raise ValueError("SHA256 mismatch: " + name)
    return len(seen)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path.cwd())
    ap.add_argument("--manifest", type=Path, default=Path(__file__).with_name("checkpoint-manifest.json"))
    args = ap.parse_args()
    count = verify(args.root, json.loads(args.manifest.read_text()))
    print(f"SOURCE_MANIFEST_PASS files={count}; source identity only")

if __name__ == "__main__": main()
