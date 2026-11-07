#!/usr/bin/env python3
"""Narrow candidate scan for simple same-line attributes omitted by census."""
import argparse, json, pathlib, re, subprocess, sys
import ledger_totals

DIRECTORY = pathlib.Path(__file__).resolve().parent
PATTERN = re.compile(r"^[ \t]*@\[[^\]\n]*\][ \t]*(?:(private|protected)[ \t]+)?(theorem|lemma|def|abbrev)[ \t]+([^\s(:]+)")

def candidates(source):
    return [(n, m.group(1), m.group(2), m.group(3))
            for n, line in enumerate(source.splitlines(), 1) if (m := PATTERN.match(line))]

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--declarations", type=pathlib.Path, required=True)
    args = p.parse_args()
    census = json.loads(args.declarations.read_text())["declarations"]
    fresh = json.loads(subprocess.check_output([sys.executable, str(DIRECTORY / "declarations.py")]))["declarations"]
    ledger_totals.validate_census(census, fresh)
    # This separate checker verifies the 48-file set and base bytes.
    subprocess.check_output([sys.executable, str(DIRECTORY / "private_header_ledger.py"), "--declarations", str(args.declarations)])
    root = pathlib.Path.cwd()
    files = sorted({row["file"] for row in census})
    rows = []
    for file in files:
        for line, modifier, kind, name in candidates((root / file).read_text()):
            rows.append({"file": file, "line": line, "modifier": modifier, "kind": kind, "name": name})
    print(json.dumps({"method": "raw textual candidates for a single simple same-line attribute; comments, nested/multiple attributes, multiline headers and other Lean syntax are not parsed", "files_scanned": len(files), "candidates": rows}, ensure_ascii=False, indent=2))

if __name__ == "__main__": main()
