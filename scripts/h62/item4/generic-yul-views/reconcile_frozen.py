#!/usr/bin/env python3
"""Reconcile EVERY frozen Controls theorem with current lexical candidates.
This preserves the original case universe; matches are not kernel or namespace
identity, semantic equivalence, accepted migrations or proof validation.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import census
from acceptance import BASE
from correspondence import frozen_blobs, source_preservation


def frozen_inventory(root, *, base=BASE):
    blobs = frozen_blobs(root, base=base)
    paths = sorted(blobs)
    request = "".join(blobs[path] + "\n" for path in paths).encode()
    output = subprocess.check_output(["git", "cat-file", "--batch"],
        input=request, cwd=root, stderr=subprocess.PIPE)
    cursor = 0
    with tempfile.TemporaryDirectory(prefix="views-frozen-") as directory:
        snapshot = Path(directory)
        for path in paths:
            end = output.index(b"\n", cursor)
            header = output[cursor:end].split()
            if len(header) != 3 or header[0].decode() != blobs[path] or header[1] != b"blob":
                raise ValueError("unexpected frozen object header: " + path)
            size = int(header[2])
            raw = output[end+1:end+1+size]
            if len(raw) != size or output[end+1+size:end+2+size] != b"\n":
                raise ValueError("truncated frozen object: " + path)
            actual = hashlib.sha1(b"blob " + str(size).encode() + b"\0" + raw).hexdigest()
            if actual != blobs[path]: raise ValueError("frozen object mismatch: " + path)
            target = snapshot / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
            cursor = end+2+size
        if cursor != len(output): raise ValueError("unexpected trailing frozen objects")
        inventory = census.scan(snapshot)
    return inventory, blobs


def reconcile(original, current):
    by_command, by_statement = collections.defaultdict(list), collections.defaultdict(list)
    for declaration in current["declarations"]:
        if declaration["kind"] != "theorem": continue
        candidate = {key: declaration[key] for key in
            ("path", "line", "name", "statement_sha256", "command_sha256", "in_controls_file")}
        by_command[candidate["command_sha256"]].append(candidate)
        by_statement[candidate["statement_sha256"]].append(candidate)
    rows, seen = [], set()
    for declaration in original["declarations"]:
        if declaration["kind"] != "theorem" or not declaration["in_controls_file"]: continue
        identity = (declaration["path"], declaration["line"], declaration["name"])
        if identity in seen: raise ValueError("duplicate frozen declaration position")
        seen.add(identity)
        candidates = by_command[declaration["command_sha256"]]
        basis = "command"
        if not candidates:
            candidates = by_statement[declaration["statement_sha256"]]
            basis = "statement"
        if not candidates:
            status = "unmatched"
        elif len(candidates) > 1:
            status = "ambiguous_" + basis + "_candidates"
        elif candidates[0]["path"] == declaration["path"]:
            status = "same_file_" + basis + "_candidate"
        else:
            status = "other_file_" + basis + "_candidate"
        original_row = {key: declaration[key] for key in
            ("path", "line", "name", "statement", "statement_sha256", "command_sha256")}
        rows.append(dict(original=original_row, status=status,
            candidates=sorted(candidates, key=lambda row: (row["path"], row["line"]))))
    if not rows: raise ValueError("empty frozen Controls theorem universe")
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    if args.output.resolve().is_relative_to(root): raise SystemExit("bulk output must be outside checkout")
    original, blobs = frozen_inventory(root)
    current = census.scan(root)
    preservation = source_preservation(root, current["files"])
    rows = reconcile(original, current)
    counts = dict(sorted(collections.Counter(row["status"] for row in rows).items()))
    result = dict(schema_version=1, status="FROZEN_SOURCE_RECONCILIATION_REPORT", base=BASE,
        boundary="One row per frozen source Controls theorem. All matches are lexical candidates only, including same-file matches. No namespace/transitive/semantic/kernel correspondence or migration acceptance is inferred.",
        parser_sha256=hashlib.sha256(Path(census.__file__).read_bytes()).hexdigest(),
        frozen_git_blobs=blobs, frozen_files=original["files"], current_files=current["files"],
        source_preservation=preservation, rows=rows,
        summary=dict(frozen_controls=len(rows), current_theorems=sum(
            declaration["kind"] == "theorem" for declaration in current["declarations"]),
            current_controls=sum(declaration["kind"] == "theorem" and declaration["in_controls_file"]
                for declaration in current["declarations"]), statuses=counts))
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result["summary"], sort_keys=True))


if __name__ == "__main__": main()
