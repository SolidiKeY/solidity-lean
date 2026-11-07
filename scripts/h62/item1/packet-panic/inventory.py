#!/usr/bin/env python3
"""Reconcile literal panicData occurrences with the separate named census.

This is a textual inventory, including comments and strings. Nearest preceding
source declaration is a navigation hint, not a Lean parse or proof of scope.
"""
import argparse
import collections
import hashlib
import json
import pathlib
import re

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
parser.add_argument("--named-census", type=pathlib.Path, required=True)
args = parser.parse_args()
root = args.root.resolve()
scan_root = root / "Solidity/Backend/PrimitivePackets"
if not scan_root.is_dir():
    parser.error(f"missing scan root: {scan_root}")
named = json.loads(args.named_census.read_text())["declarations"]
expected = collections.Counter((entry["file"], entry["line"], entry["declaration"]) for entry in named)
if not expected:
    parser.error("empty named census cannot be reconciled")
if any(count != 1 for count in expected.values()):
    parser.error("duplicate named census entries")
by_line = collections.defaultdict(list)
for path, line, name in expected:
    by_line[path, line].append(name)

declaration = re.compile(r"^[ \t]*(?:(?:private|protected)[ \t]+)?(?:theorem|lemma|def|abbrev|example)[ \t]+([^\s(:]+)")
occurrences = []
matched = collections.Counter()
for path in sorted(scan_root.rglob("*.lean")):
    rel = path.relative_to(root).as_posix()
    data = path.read_bytes()
    source = data.decode("utf-8")
    source_hash = hashlib.sha256(data).hexdigest()
    hint = None
    for line_no, line in enumerate(source.splitlines(), 1):
        found = declaration.match(line)
        if found:
            hint = found.group(1)
        for match in re.finditer(r"\bpanicData\b", line):
            names = by_line.get((rel, line_no), [])
            for name in names:
                if found is None or found.group(1) != name:
                    parser.error(f"named declaration not on occurrence line at {rel}:{line_no}: {name}")
                matched[rel, line_no, name] += 1
            tail = line[match.end():]
            code = re.match(r"\s*\.([A-Za-z][A-Za-z0-9_]*)", tail)
            occurrences.append({"file": rel, "sha256": source_hash, "line": line_no,
                                "column": match.start() + 1, "text": line.strip(),
                                "nearest_declaration_hint": hint,
                                "panic_code_hint": code.group(1) if code else None,
                                "named_controls_on_line": names})
if matched != expected:
    parser.error(f"named census reconciliation failed: missing={list((expected-matched).elements())}; extra={list((matched-expected).elements())}")
counts = collections.Counter("named_control" if row["named_controls_on_line"] else "other_reference" for row in occurrences)
print(json.dumps({"method": "literal textual occurrences, including comments and strings; nearest declaration and panic code are hints, not Lean parsing or semantic case coverage",
                  "named_census_count": len(named), "counts": dict(sorted(counts.items())),
                  "occurrences": occurrences}, indent=2, ensure_ascii=False))
