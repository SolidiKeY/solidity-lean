#!/usr/bin/env python3
"""Deterministic frozen-source candidates; NOT an elaborated statement census.

Include every module-map row and expand globs. Retain complete original files,
including namespace/section variables, so a later elaborated census can recover
implicit premises. Every lexical theorem candidate remains unresolved until Lean
reflection confirms its signature, hypotheses, identity, visibility and owner.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    args = parser.parse_args()
    root = pathlib.Path(subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"], text=True).strip())
    def frozen(path):
        return subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=root).decode()
    tracked = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE], cwd=root, text=True).splitlines()
    import fnmatch
    modules = {}
    missing = []
    for area in ("typing", "frontend"):
        mapping = frozen(f"docs/module-map/{area}.md")
        for token in re.findall(r"^\| `([^`]+\.lean)`", mapping, re.M):
            pattern = token if token in tracked else "Solidity/" + token
            matches = sorted(p for p in tracked
                if len(p.split("/")) == len(pattern.split("/"))
                and all(fnmatch.fnmatchcase(part, pat)
                    for part, pat in zip(p.split("/"), pattern.split("/"))))
            if not matches:
                missing.append({"area": area, "pattern": pattern})
            for path in matches:
                modules.setdefault(path, []).append(area)
    records = []
    for path, areas in sorted(modules.items()):
        source = frozen(path)
        candidates = [
            {"line": source.count("\n", 0, m.start()) + 1,
             "source_name": m.group(2), "kind": m.group(1),
             "status": "unresolved-lexical-candidate",
             "owner": None, "simultaneous_witness": None}
            for m in re.finditer(r"\b(theorem|lemma)\s+([^\s({:]+)", source)
        ]
        records.append({"path": path, "areas": sorted(set(areas)),
            "sha256": hashlib.sha256(source.encode()).hexdigest(),
            "source": source, "candidates": candidates})
    result = {"base": BASE, "classification": "source-backfill-only",
        "limitations": ["Lexical candidates include comments and strings and may miss macro declarations.",
            "Names are source spellings, not verified fully qualified Lean names.",
            "No signature, premise satisfiability, owner or coverage certification is claimed."],
        "missing_patterns": missing, "modules": records}
    args.output.write_text(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"modules": len(records), "lexical_candidates": sum(len(r["candidates"]) for r in records),
        "missing_patterns": missing, "output": str(args.output)}, sort_keys=True))

if __name__ == "__main__":
    main()
