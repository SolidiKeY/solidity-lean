#!/usr/bin/env python3
"""Guard against crediting fresh source recovery as historical ownership replay.

Reuse the frozen scanner. No owner registry, historical receipt, Lean elaboration
or witness is inferred. This separate command does not relax census.generate's
original authenticated-ownership requirement. Bulk output stays outside Git.
"""
import argparse
import json
import re
from pathlib import Path
from census import AREAS, BASE, git, scan, sha


def generate():
    files = set(git("ls-tree", "-r", "--name-only", BASE).decode().splitlines())
    modules, maps = {}, {}
    for area in AREAS:
        path = f"docs/module-map/{area}.md"
        raw = git("show", f"{BASE}:{path}")
        maps[path] = sha(raw)
        for line in raw.decode().splitlines():
            if not line.startswith("| "):
                continue
            for ref in re.findall(r"`([^`]+\.lean)`", line.split("|")[1]):
                hits = [p for p in (ref, "Solidity/" + ref) if p in files]
                if len(hits) != 1:
                    raise ValueError(f"unresolved or ambiguous module: {ref}")
                modules.setdefault(hits[0], set()).add(area)
    sources, rows = {}, []
    for path, areas in sorted(modules.items()):
        raw = git("show", f"{BASE}:{path}")
        sources[path] = {"sha256": sha(raw), "areas": sorted(areas)}
        for row in scan(path, raw, areas):
            row["owner"] = None
            row["owner_status"] = "UNVERIFIABLE-historical-snapshot"
            rows.append(row)
    if len({r["id"] for r in rows}) != len(rows):
        raise ValueError("duplicate source declaration identity")
    return {"base": BASE, "method": "fresh-frozen-source-only",
            "historical_ownership": "UNVERIFIABLE", "historical_replay": False,
            "kernel_checked": False, "certified_witnesses": 0,
            "maps": maps, "sources": sources, "declarations": rows,
            "summary": {"files": len(sources), "source_candidates": len(rows)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[4]
    if args.output.resolve().is_relative_to(repo):
        raise ValueError("source census bulk output must remain outside checkout")
    if args.output.exists() or args.output.is_symlink():
        raise ValueError("refusing existing output")
    report = generate()
    payload = (json.dumps(report, sort_keys=True, ensure_ascii=False) + "\n").encode()
    with args.output.open("xb") as stream:
        stream.write(payload)
    print(json.dumps({**report["summary"], "sha256": sha(payload),
                      "historical_replay": False, "certified_witnesses": 0}))


if __name__ == "__main__":
    main()
