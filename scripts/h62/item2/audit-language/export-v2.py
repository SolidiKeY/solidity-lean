#!/usr/bin/env python3
"""Export v2 using an explicit, pinned private historical request.

--historical-input-root is the external directory containing tests/h62/... from
private archive fa68e0ac599d1f6a59dab0af5b19dbf2ae029c9f. No download or fallback
occurs. The request is historical report data, not current authority or proof.
The legacy exporter retains its original branch/base/clean-tree/scope guards.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

SPEC = importlib.util.spec_from_file_location("audit_language_export_v1", Path(__file__).with_name("export.py"))
legacy = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(legacy)
REQUEST = "tests/h62/item2/audit-language/owner-resolution-request.json"
REQUEST_BYTES = 1477
REQUEST_SHA256 = "45666be1711a6b63c303b3fe9d3bfa04e1bf4e349f07a56a202144ba3feda41d"


def load_historical_request(directory):
    root = directory.resolve()
    if root.is_relative_to(legacy.ROOT.resolve()):
        raise ValueError("Historical input root must be outside the repository")
    path = (root / REQUEST).resolve(strict=True)
    if not path.is_relative_to(root):
        raise ValueError("Historical request escapes its input root")
    raw = path.read_bytes()
    if len(raw) != REQUEST_BYTES or hashlib.sha256(raw).hexdigest() != REQUEST_SHA256:
        raise ValueError("Historical request checksum mismatch: " + REQUEST)
    return json.loads(raw)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--historical-input-root", type=Path, required=True)
    a = p.parse_args()
    request = load_historical_request(a.historical_input_root)
    legacy.export(a.output, owner_request=request)


if __name__ == "__main__":
    main()
