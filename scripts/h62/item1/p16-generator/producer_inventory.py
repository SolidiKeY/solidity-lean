#!/usr/bin/env python3
"""List every changed Yul Lean file at a specified descendant commit."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

import census
import generate
from conservation import BASE


def git(root, *args):
    return subprocess.run(["git", "--no-replace-objects", *args], cwd=root, capture_output=True, check=True).stdout


def collect_changes(root, base, head):
    tokens = git(root, "diff", "--name-status", "-z", "--no-renames", base, head, "--", "Solidity/Yul").split(b"\0")
    tokens = [x.decode("utf-8") for x in tokens if x]
    if len(tokens) % 2:
        raise ValueError("unexpected git diff record")
    rows = []
    for status, path in zip(tokens[::2], tokens[1::2]):
        if not path.endswith(".lean"):
            continue
        if status not in ("A", "M", "D", "T"):
            raise ValueError("unsupported Git change status " + status)
        mode = None
        object_type = None
        if status != "D":
            record = git(root, "ls-tree", "-z", head, "--", path)
            records = [item for item in record.split(b"\0") if item]
            if len(records) != 1 or b"\t" not in records[0]:
                raise ValueError("missing or ambiguous Git tree entry " + path)
            metadata, found = records[0].split(b"\t", 1)
            fields = metadata.split()
            if len(fields) != 3 or found != path.encode("utf-8"):
                raise ValueError("unexpected Git tree entry " + path)
            mode, object_type = fields[0].decode("ascii"), fields[1].decode("ascii")
        data = git(root, "show", head + ":" + path) if object_type == "blob" else None
        module = path[:-5].replace("/", ".")
        rows.append({"path": path, "change": status, "mode": mode, "object_type": object_type,
                     "sha256": None if data is None else hashlib.sha256(data).hexdigest(),
                     "module": module if generate.MODULE.fullmatch(module) else None})
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--head", required=True, help="full owner commit SHA")
    ap.add_argument("--owner", choices=("VY1", "VY3"), required=True)
    args = ap.parse_args()
    if not re.fullmatch(r"[0-9a-f]{40}", args.head):
        raise ValueError("head must be a full lowercase commit SHA")
    git(generate.ROOT, "merge-base", "--is-ancestor", BASE, args.head)
    baseline = git(generate.ROOT, "show", BASE + ":" + generate.NAME).decode("utf-8")
    observed = git(generate.ROOT, "show", args.head + ":" + generate.NAME).decode("utf-8")
    baseline_imports, _ = census.parse(baseline)
    imports, _ = census.parse(observed)
    generate.render(require_sources=False)
    registrations = {}
    for path in sorted((generate.HERE / "registrations").glob("*.json")):
        item = json.loads(path.read_bytes())
        if item["module"] is not None:
            registrations.setdefault(item["module"], []).append(path.stem)
    rows = collect_changes(generate.ROOT, BASE, args.head)
    for row in rows:
        module = row["module"]
        row["imported_at_base"] = module in baseline_imports
        row["imported_at_head"] = module in imports
        row["registrations"] = registrations.get(module, [])
        row["requires_owner_membership_review"] = row["path"] != generate.NAME
    result = {"owner_label": args.owner, "head": args.head, "base": BASE,
              "p16_sha256": hashlib.sha256(observed.encode("utf-8")).hexdigest(),
              "changed_yul_lean_files": rows,
              "candidate_count": sum(row["requires_owner_membership_review"] for row in rows),
              "status": "owner_review_required",
              "limitation": "This is only the net Solidity/Yul Lean-file tree diff: it excludes unchanged files, reverted edits and producers outside that path. Git records do not establish producer membership, ownership, or owner approval; every candidate requires an owner decision."}
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as exc:
        print("P16 producer inventory: " + str(exc), file=sys.stderr)
        sys.exit(2)
