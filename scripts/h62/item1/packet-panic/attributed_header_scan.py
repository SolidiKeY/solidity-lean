#!/usr/bin/env python3
"""Lexical attributed-header candidates; this is not a Lean parser."""
import argparse, json, pathlib, re, subprocess, sys
import ledger_totals
from lexical_mask import mask_comments_and_strings

DIRECTORY = pathlib.Path(__file__).resolve().parent
DECLARATION = re.compile(r"(?:(private|protected)[ \t\n]+)?(?:noncomputable[ \t\n]+)?(theorem|lemma|def|abbrev)[ \t\n]+([^\s(:]+)")

def candidates(source):
    masked = mask_comments_and_strings(source, mask_attributes=False)
    result = []
    i = 0
    while i < len(masked):
        start = masked.find("@[", i)
        if start < 0:
            break
        cursor = start
        while masked[cursor:cursor + 2] == "@[":
            cursor += 2
            depth = 1
            while cursor < len(masked) and depth:
                if masked[cursor] == "[": depth += 1
                elif masked[cursor] == "]": depth -= 1
                cursor += 1
            if depth:
                raise ValueError("unterminated attribute")
            while cursor < len(masked) and masked[cursor].isspace(): cursor += 1
        match = DECLARATION.match(masked, cursor)
        if match:
            declaration_start = match.start(2)
            line = source.count("\n", 0, declaration_start) + 1
            column = declaration_start - source.rfind("\n", 0, declaration_start)
            result.append((line, column, match.group(1), match.group(2), match.group(3)))
            i = match.end()
        else:
            i = cursor
    return result

def census_covers(census, file, line, kind, name):
    return any(r["file"] == file and r["line"] == line and r["kind"] == kind and r["name"] == name for r in census)

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
        for line, column, modifier, kind, name in candidates((root / file).read_text()):
            rows.append({"file": file, "line": line, "column": column, "modifier": modifier,
                         "kind": kind, "name": name,
                         "original_census_covered": census_covers(census, file, line, kind, name)})
    print(json.dumps({"method": "masked lexical candidates after nested, multiple or multiline attributes; comments and strings are masked, columns are Unicode code-point offsets, and other modifiers or Lean syntax may be missed or misidentified; not a Lean parser", "files_scanned": len(files), "candidates": rows}, ensure_ascii=False, indent=2))

if __name__ == "__main__": main()
