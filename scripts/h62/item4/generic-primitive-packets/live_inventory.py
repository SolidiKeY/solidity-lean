#!/usr/bin/env python3
"""Reconcile frozen original files with explicit live additions; lexical evidence only.

The original byte-fidelity gate stays unchanged. This companion reports every
additional file without counting it as an original case or semantic coverage.
"""
import argparse
import json
import subprocess
from pathlib import Path
from census import BASE, FAMILY, ROOT, collect, digest


def reconcile(data, frozen):
    files = {row["path"]: row for row in data["files"]}
    if len(files) != len(data["files"]):
        raise ValueError("duplicate current file")
    missing = sorted(set(frozen) - set(files))
    changed = sorted(p for p in frozen if p in files and frozen[p] != files[p]["sha256"])
    if missing or changed:
        raise ValueError(f"frozen originals missing={missing}, changed={changed}")
    originals = [r for r in data["declarations"] if r["path"] in frozen]
    additions = [{**files[p], "declarations": [r for r in data["declarations"] if r["path"] == p]}
                 for p in sorted(set(files) - set(frozen))]
    return dict(base=BASE, original_files=len(frozen), original_declarations=len(originals),
                original_bytes_unchanged=True, live_summary=data["summary"],
                additions=additions,
                boundary="Lexical/source-byte accounting only; additions are explicit, not original cases or proof coverage.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    paths = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE, "--", FAMILY],
                                    cwd=ROOT, text=True).splitlines()
    frozen = {p: digest(subprocess.check_output(["git", "show", f"{BASE}:{p}"], cwd=ROOT))
              for p in paths if p.endswith(".lean")}
    if not frozen:
        raise ValueError("empty frozen inventory")
    report = reconcile(collect(ROOT), frozen)
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "additions"}, sort_keys=True))
    print("explicit additional files:", len(report["additions"]))


if __name__ == "__main__":
    main()
