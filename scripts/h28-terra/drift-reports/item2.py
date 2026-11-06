#!/usr/bin/env python3
"""Report missing file evidence for selected feature statuses."""
import json
import sys


def report(data):
    files = data.get("files", [])
    if (not isinstance(files, list) or any(
        not isinstance(f, dict) or not isinstance(f.get("path"), str)
        or not isinstance(f.get("text"), str) for f in files
    ) or len({f["path"] for f in files}) != len(files)):
        return {"error": "invalid-or-duplicate-files"}
    by_path = {f["path"]: f["text"] for f in files}
    manifest = json.loads(by_path.get("docs/solidity-features.json", "{\"features\":[]}"))
    return [{"id": feature["id"], "status": feature.get("current"),
             "scope": feature.get("scope"),
             "missingEvidence": sorted(p for p in feature.get("localEvidence", []) if p not in by_path),
             "verdict": "owner-review-required-no-status-rewrite"}
            for feature in manifest["features"]
            if feature.get("current") in ["partial", "missing", "unsupported"]]


if __name__ == "__main__":
    json.dump(report(json.load(sys.stdin)), sys.stdout)
    print()
