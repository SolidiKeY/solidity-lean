#!/usr/bin/env python3
"""Verify v2 with two exact private historical summaries, never proof acceptance.

--historical-input-root contains the tests/h62/... paths from private archive
fa68e0ac599d1f6a59dab0af5b19dbf2ae029c9f. Other catalog files remain repository
inputs. There is no download or fallback to the removed repository summaries.
Bulk integrity checks and --require-bulk unavailable/failure behavior are v1's.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

SPEC = importlib.util.spec_from_file_location("portable_evidence_v1", Path(__file__).with_name("verify-portable-evidence.py"))
legacy = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(legacy)
PINS = {
    "tests/h62/item6/migrate-solkey/portable-evidence/old-api-summary.json":
        (1117, "d2c695899dbdc3ac7c90ab4a2cb6f4e6bf2a6ed3f040ad977ad9fdd5a41e2b9a"),
    "tests/h62/item6/migrate-solkey/portable-evidence/sdk-summary.json":
        (879, "b6b45e6ef3463cffebabae36705955dc6aa0b0d0df265c1575687fe74cf46fc6"),
}


def verify(directory, artifact_dir=None):
    root = directory.resolve()
    if root.is_relative_to(legacy.ROOT.resolve()):
        raise ValueError("Historical input root must be outside the repository")
    catalog = legacy.load_catalog()
    selected = [r for r in catalog["repository_files"] if r["path"] in PINS]
    if len(selected) != len(PINS) or {r["path"] for r in selected} != set(PINS):
        raise ValueError("Historical summary catalog membership mismatch")
    for row in selected:
        if row["sha256"] != PINS[row["path"]][1]:
            raise ValueError("Historical summary catalog checksum mismatch: " + row["path"])

    def read_digest(row):
        name = row["path"]
        if name not in PINS:
            return legacy.repository_digest(row)
        path = (root / name).resolve(strict=True)
        if not path.is_relative_to(root):
            raise ValueError("Historical summary escapes its input root: " + name)
        raw = path.read_bytes()
        size, expected = PINS[name]
        actual = hashlib.sha256(raw).hexdigest()
        if len(raw) != size or actual != expected:
            raise ValueError("Historical summary checksum mismatch: " + name)
        return actual

    report = legacy.verify(catalog, artifact_dir, read_digest=read_digest)
    del report["repository_summaries"]
    return {"interface_version": 2, "historical_summaries": "verified",
            "repository_support_files": "verified", **report}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--historical-input-root", type=Path, required=True)
    p.add_argument("--artifact-dir", type=Path)
    p.add_argument("--require-bulk", action="store_true")
    a = p.parse_args()
    report = verify(a.historical_input_root, a.artifact_dir)
    print(json.dumps(report, indent=2))
    if a.require_bulk and any(s["status"] != "verified" for s in report["bulk"]):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
