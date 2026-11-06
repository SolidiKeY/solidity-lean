#!/usr/bin/env python3
"""Derive candidate Lake contexts from every census row; no path is excluded."""
import collections
import importlib.util
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("h55_census", ROOT / "scripts/h55/module-times/census.py")
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
IDENT = re.compile(r"^[A-Za-z_][A-Za-z_0-9\x27]*$")
ROOT_MODULES = {"Solidity.lean", "SolidityExamples.lean", "SoliditySlowExamples.lean", "SolidityCorpus.lean",
                "SolkeyTestSuite.lean", "SolkeyCheck.lean", "SolidityLean.lean",
                "SolCases.lean", "TrustAudit.lean"}


def candidate(row):
    path = row["path"]
    result = dict(row)
    result.update(context=None, module=None, resolution="review")
    if path.startswith("Solidity/") or path in ROOT_MODULES:
        context, relative = "root", path
    elif path.startswith("Bridge/vendor/"):
        context, relative = "bridge-vendor", path[len("Bridge/vendor/"):]
    elif path.startswith("Bridge/") and not path.startswith("Bridge/tests/"):
        context, relative = "bridge", path[len("Bridge/"):]
    elif path.startswith("vendor/LeanTeX/"):
        context, relative = "root-vendor", path[len("vendor/LeanTeX/"):]
        # srcDir is vendor/LeanTeX, verify any candidate against actual lake config.
    else:
        result["context"] = "standalone-bridge-review" if path.startswith("Bridge/tests/") else "standalone-root-review"
        result["resolution"] = "file-check-review"
        return result
    parts = relative[:-5].split("/")
    result["context"] = context
    if all(IDENT.fullmatch(part) for part in parts):
        result["module"] = ".".join(parts)
        result["resolution"] = "candidate-review"
    return result


def derive(rows):
    out = [candidate(row) for row in rows]
    # All contexts are potential search-path peers (Bridge depends on root);
    # a collision is a conservative review warning, not a resolution claim.
    names = collections.Counter(row["module"] for row in out if row["module"])
    for row in out:
        row["collision"] = bool(row["module"] and names[row["module"]] > 1)
    return out


def main():
    if len(sys.argv) != 1:
        print("usage: mapping.py", file=sys.stderr)
        return 2
    try:
        print(json.dumps(derive(census.census(ROOT)), indent=2))
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"mapping failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
