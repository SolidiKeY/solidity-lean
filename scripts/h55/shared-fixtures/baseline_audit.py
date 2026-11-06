#!/usr/bin/env python3
"""Compare every byte of explicitly named Lean inputs with a Git baseline.

Exit 0 only when every input is identical, 1 when any differs, 2 for invalid
scope or inaccessible input. Changed files always need further acceptance.
This is a conservative review aid, not a Lean declaration/type parser.
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = "4d3790eadb8a5212233bc7d5e345817476b2f590"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", help="explicit repository-relative .lean input paths")
    args = parser.parse_args()
    if len(set(args.paths)) != len(args.paths):
        parser.error("duplicate paths are not allowed")
    rows = []
    for name in sorted(args.paths):
        path = pathlib.PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or str(path) != name or path.suffix != ".lean":
            parser.error(f"invalid repository-relative Lean path: {name}")
        current = ROOT.joinpath(*path.parts)
        try:
            resolved = current.resolve(strict=True)
            if not resolved.is_relative_to(ROOT) or not resolved.is_file():
                raise ValueError("not a file inside the repository")
            before = subprocess.run(["git", "show", f"{BASE}:{name}"], cwd=ROOT,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout
            after = resolved.read_bytes()
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            print(f"cannot audit {name}: {error}", file=sys.stderr)
            return 2
        rows.append({"path": name, "baseline_sha256": digest(before),
                     "current_sha256": digest(after), "identical": before == after})
    print(json.dumps({"baseline": BASE, "files": rows,
                      "limitation": "Byte identity only; changed files require declaration, case, proof and review gates."},
                     indent=2, sort_keys=True))
    return int(any(not row["identical"] for row in rows))


if __name__ == "__main__":
    raise SystemExit(main())
