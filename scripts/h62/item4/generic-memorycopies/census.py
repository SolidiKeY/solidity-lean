#!/usr/bin/env python3
"""Source-byte census, not a Lean parser or theorem equivalence proof.

Every family file is pinned in full. All declarations additionally retain
exact header bytes (through the depth-zero :=), line and byte offsets. Comments
and strings are masked without changing offsets; ambiguous headers fail closed.
Outputs are deterministic JSON; bulk evidence belongs outside Git.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

FAMILY = Path("Solidity/Backend/MemoryCopies")
DECL = re.compile(r"(?m)^(?:(?:private|protected|noncomputable|unsafe|partial) +)*(theorem|lemma|def|abbrev|opaque|instance|structure|inductive)\s+([^\s:({]+)")
BOUNDARY = re.compile(r"(?m)^(?:end(?:\s|$)|namespace\s|section(?:\s|$)|#)")

def sha(data):
    return hashlib.sha256(data).hexdigest()

def mask(text):
    out = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated comment")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError("unterminated string")
        else:
            i += 1
            continue
        for j in range(start, i):
            if out[j] != "\n":
                out[j] = " "
    return "".join(out)

def declarations(text):
    clean = mask(text)
    matches = list(DECL.finditer(clean))
    result = []
    for index, found in enumerate(matches):
        limit = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        boundary = BOUNDARY.search(clean, found.end(), limit)
        if boundary:
            limit = boundary.start()
        stack = []
        finish = None
        lets = 0
        type_match = False
        for i in range(found.end(), limit):
            c = clean[i]
            if c in "({[⟨":
                stack.append(c)
            elif c in ")}]⟩":
                if not stack:
                    raise ValueError("unbalanced header: " + found[2])
                expected = {')': '(', '}': '{', ']': '[', '⟩': '⟨'}[c]
                if stack.pop() != expected:
                    raise ValueError("mismatched header delimiter: " + found[2])
            elif not stack and re.match(r"match\b", clean[i:]):
                type_match = True
            elif not stack and re.match(r"let(?:I)?\b", clean[i:]) and (i == 0 or not clean[i - 1].isalnum()):
                lets += 1
            elif not stack and clean.startswith(":=", i):
                if lets:
                    lets -= 1
                    continue
                finish = i
                break
            elif not stack and not type_match and c == "|" and not clean[clean.rfind("\n", 0, i) + 1:i].strip():
                finish = i
                break
            elif not stack and (clean.startswith(" where", i) or clean.startswith("\nwhere", i)):
                finish = i
                break
        if finish is None:
            raise ValueError("unrecognized declaration header: " + found[2])
        header = text[found.start():finish]
        result.append(dict(kind=found[1], name=found[2], line=text.count("\n", 0, found.start()) + 1,
                           byte_start=len(text[:found.start()].encode()),
                           byte_end=len(text[:finish].encode()), header=header,
                           header_sha256=sha(header.encode()),
                           source_region_sha256=sha(text[found.start():limit].encode())))
    return result

def census(root):
    files = []
    for path in sorted((root / FAMILY).rglob("*.lean")):
        data = path.read_bytes()
        controls = "Controls" in path.stem
        ds = declarations(data.decode())
        files.append(dict(path=path.relative_to(root).as_posix(), sha256=sha(data),
                          bytes=len(data), controls=controls, declarations=ds))
    if not files:
        raise ValueError("empty family")
    return dict(schema=1, family=str(FAMILY), files=files,
                counts=dict(files=len(files), controls=sum(f["controls"] for f in files),
                            declarations=sum(len(f["declarations"]) for f in files),
                            theorems=sum(d["kind"] in ("theorem", "lemma") for f in files for d in f["declarations"])))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path, help="compare complete frozen inventory, including headers")
    args = parser.parse_args()
    report = census(args.root)
    data = (json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()
    if args.check and data != args.check.read_bytes():
        raise SystemExit("CENSUS_FAIL: frozen family or header bytes changed")
    if args.output:
        args.output.write_bytes(data)
    print(json.dumps(dict(status="CENSUS_PASS", sha256=sha(data), **report["counts"]), sort_keys=True))

if __name__ == "__main__":
    main()
