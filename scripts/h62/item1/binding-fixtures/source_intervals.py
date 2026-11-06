#!/usr/bin/env python3
"""Capture exact source intervals for the named relation controls.

Markers are lexical, not parsed Lean declarations. The complete file is the
preamble followed by the interval texts, in order; commands, comments and proofs
are retained. Keep generated output outside Git.
"""
import hashlib
import json
import pathlib
import re
import sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lexical import code_only, unknown_identifiers
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[4]
MARKER = re.compile(r"^(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|inductive|structure)\s+([^\s:(]+)")


def split_source(data):
    lines = data.splitlines(keepends=True)
    starts = [(i, match.group(1), match.group(2)) for i, line in enumerate(code_only(data).splitlines(keepends=True))
              if (match := MARKER.match(line))]
    preamble = "".join(lines[:starts[0][0]]) if starts else data
    intervals = []
    for index, (start, kind, name) in enumerate(starts):
        end = starts[index + 1][0] if index + 1 < len(starts) else len(lines)
        text = "".join(lines[start:end])
        intervals.append({"start_line": start + 1, "end_line": end,
                          "kind": kind, "name": name, "text": text,
                          "sha256": hashlib.sha256(text.encode()).hexdigest()})
    return preamble, intervals


def main():
    rec = ROOT / "scripts/h62/item1/binding-fixtures/reconcile.py"
    source = json.loads(subprocess.check_output([sys.executable, str(rec)], cwd=ROOT))
    files = []
    for row in source["relation_controls"]:
        raw = (ROOT / row["path"]).read_bytes()
        data = raw.decode("utf-8")
        preamble, intervals = split_source(data)
        files.append({"path": row["path"], "sha256": hashlib.sha256(raw).hexdigest(),
                      "preamble": preamble, "intervals": intervals,
                      "unknown_quoted_identifiers": unknown_identifiers(data)})
    print(json.dumps({"format": 1, "method": "lexical markers; not Lean parsing", "files": files},
                     indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
