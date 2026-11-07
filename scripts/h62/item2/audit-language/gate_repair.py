#!/usr/bin/env python3
"""Authenticate the exact user-requested gate-repair proof revisions.
Historical producer receipts stay unchanged. No patch application or proof claim.
"""
import hashlib
import json
from pathlib import Path
from census import BASE, git
from overlay_review import TRUSTED, reconstruct, fidelity, receipt_patch_path

ROOT = Path(__file__).resolve().parents[4]
MANIFEST = ROOT / "tests/h62/item2/audit-language/gate-repair-manifest.json"

def approved_revisions(manifest_path):
    assert Path(manifest_path).resolve() == MANIFEST, "unregistered repair manifest"
    manifest = json.loads(MANIFEST.read_text())
    assert manifest["schema_version"] == 1 and manifest["original_base"] == BASE
    rows = manifest["revisions"]
    allowed = {row["path"] for row in TRUSTED.values()}
    assert len(rows) == len(allowed) and {r["path"] for r in rows} == allowed
    results = {}
    for row in rows:
        path = row["path"]
        patch_path = receipt_patch_path({
            "path": row["patch_path"],
            "path_relative_to_evidence": row["patch_relative_to_evidence"],
        })
        patch = patch_path.read_bytes()
        assert hashlib.sha256(patch).hexdigest() == row["patch_sha256"]
        assert len(patch) == row["patch_bytes"]
        original = git("show", BASE + ":" + path)
        approved, *_ = reconstruct(patch, original, path)
        fidelity(path, original, approved)
        assert hashlib.sha256(approved).hexdigest() == row["source_sha256"]
        assert (ROOT / path).read_bytes() == approved
        results[path] = approved
    return results
