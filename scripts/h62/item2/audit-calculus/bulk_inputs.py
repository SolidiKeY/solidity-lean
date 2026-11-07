"""Regression guard: moved frozen inputs must retain exact bytes and fail closed."""
import hashlib
import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
MANIFEST = REPO / "tests/h62/item2/audit-calculus/bulk-inputs-manifest.json"


def bulk_bytes(name, manifest=MANIFEST):
    row = json.loads(manifest.read_text())[name]
    path = Path(row["path"])
    if not path.is_absolute() or path.resolve().is_relative_to(REPO):
        raise ValueError("H44: bulk input must be an absolute external path")
    data = path.read_bytes()
    if len(data) != row["bytes"] or hashlib.sha256(data).hexdigest() != row["sha256"]:
        raise ValueError("bulk input size/checksum mismatch: " + name)
    return data
