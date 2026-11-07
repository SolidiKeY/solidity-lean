#!/usr/bin/env python3
"""Reproduce the H44 external scope inventory from its pinned frozen census."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
MANIFEST = ROOT / "tests/h62/item2/audit-language/retirement/scope-manifest.json"

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--census", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    scope = manifest["scope"]
    raw = a.census.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == scope["frozen_exact_manifest_sha256"]
    census = json.loads(raw)
    assert census["base"] == scope["base"]
    assert census["maps"] == scope["frozen_module_maps"]
    assert len(census["sources"]) == scope["mapped_files"] == 389
    assert len(census["declarations"]) == scope["source_candidates"] == 4146
    full = dict(scope, frozen_files=census["sources"])
    result = (json.dumps(full, indent=2, sort_keys=True) + "\n").encode()
    assert hashlib.sha256(result).hexdigest() == manifest["artifact"]["sha256"]
    assert len(result) == manifest["artifact"]["bytes"]
    assert not a.output.resolve().is_relative_to(ROOT), "bulk output must stay off Git"
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_bytes(result)
    print(json.dumps({"status": "PASS-exact-scope-reproduction", "output": str(a.output.resolve()),
                      "bytes": len(result), "sha256": hashlib.sha256(result).hexdigest()}))

if __name__ == "__main__":
    main()
