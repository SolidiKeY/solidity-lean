#!/usr/bin/env python3
"""Conservative source census; hashes are textual pins, not semantic proofs.

All family files and declarations are retained. Control theorem rows deliberately
include private helpers: classification never silently drops a possible case.
Comment/string masking preserves character offsets, including nested comments.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

FAMILY = "Solidity/Backend/StorageOps"
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
ROOT = Path(__file__).resolve().parents[4]
DEST = ROOT / "tests/h62/item4/generic-storageops/inventory-manifest.json"
COMMAND = re.compile(r"^(?:(?:private|protected|noncomputable|unsafe|partial) +)*(?:def|abbrev|theorem|lemma|structure|inductive|instance|opaque|axiom|constant|namespace|section|mutual|variable|universe|end|open|import|attribute|set_option)\b|^#", re.M)
DECL = re.compile(r"(?P<mods>(?:(?:private|protected|noncomputable|unsafe|partial) +)*)(?P<kind>def|abbrev|theorem|lemma|structure|inductive|instance|opaque|axiom|constant)\s+(?P<name>[^\s:({]+)")

def digest(s):
    return hashlib.sha256(s.encode()).hexdigest()

def mask(source, preserve_newlines=True):
    out = list(source)
    i = 0
    depth = 0
    string = False
    while i < len(source):
        pair = source[i:i+2]
        if depth:
            if pair == "/-":
                out[i:i+2] = "  "; depth += 1; i += 2
            elif pair == "-/":
                out[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if not preserve_newlines or source[i] != "\n": out[i] = " "
                i += 1
        elif string:
            if source[i] == "\\":
                out[i] = " "; i += 1
                if i < len(source): out[i] = " "; i += 1
            elif source[i] == '"':
                out[i] = " "; string = False; i += 1
            else:
                if not preserve_newlines or source[i] != "\n": out[i] = " "
                i += 1
        elif pair == "/-":
            out[i:i+2] = "  "; depth = 1; i += 2
        elif pair == "--":
            while i < len(source) and source[i] != "\n": out[i] = " "; i += 1
        elif source[i] == '"':
            out[i] = " "; string = True; i += 1
        else:
            i += 1
    if depth or string: raise ValueError("Unterminated comment or string")
    return "".join(out)

def legacy_signature_end(code):
    stack = []
    for i, c in enumerate(code):
        if c in "([{⟨": stack.append(c)
        elif c in ")] }⟩".replace(" ", ""):
            if stack: stack.pop()
        elif not stack and (code[i:i+2] == ":=" or c == "|" or
                            re.match(r"where\b", code[i:])):
            return i
    return len(code)

def signature_end(code):
    """Find declaration assignment, skipping assignments inside proposition lets."""
    stack = []
    pending_lets = 0
    for i, c in enumerate(code):
        if c in "([{⟨": stack.append(c)
        elif c in ")] }⟩".replace(" ", ""):
            if stack: stack.pop()
        elif not stack:
            boundary = i == 0 or not (code[i-1].isalnum() or code[i-1] in "_'.«")
            if boundary and re.match(r"let\b", code[i:]):
                pending_lets += 1
            elif code[i:i+2] == ":=":
                if pending_lets: pending_lets -= 1
                else: return i
            elif c == "|" or (boundary and re.match(r"where\b", code[i:])):
                return i
    return len(code)


def declarations(source, path):
    code = mask(source)
    commands = list(COMMAND.finditer(code))
    namespaces = []
    sections = []
    context = []
    rows = []
    for j, command in enumerate(commands):
        start = command.start()
        stop = commands[j+1].start() if j+1 < len(commands) else len(code)
        chunk = code[start:stop]
        if chunk.startswith("namespace "):
            namespaces.append(chunk.split()[1]); sections.append(("namespace",len(context))); continue
        if re.match(r"(?:section|mutual)\b", chunk):
            sections.append((chunk.split()[0],len(context))); continue
        if re.match(r"(?:variable|universe)\b", chunk):
            context.append(source[start:stop].rstrip()); continue
        if re.match(r"end\b", chunk):
            if sections:
                kind, count = sections.pop()
                del context[count:]
                if kind == "namespace": namespaces.pop()
            continue
        d = DECL.match(chunk)
        if not d: continue
        end = start + signature_end(chunk)
        statement = source[start:end].rstrip()
        legacy = source[start:start+legacy_signature_end(chunk)].rstrip()
        # Exclude trailing comments from proof/body hash by using next command;
        # whole-file hash remains the authoritative complete preservation pin.
        rows.append(dict(path=path, name=".".join(namespaces+[d["name"]]),
            kind=d["kind"], private="private" in d["mods"].split(),
            line=source.count("\n", 0, start)+1,
            control_file=Path(path).stem.endswith("Controls"),
            candidate_case=Path(path).stem.endswith("Controls") and d["kind"] in ("theorem", "lemma"),
            statement=statement, header_sha256=digest(statement),
            ambient_binders=list(context),
            statement_sha256=digest("\n".join(context+[statement])),
            legacy_v1_statement_sha256=digest("\n".join(context+[legacy])),
            declaration_sha256=digest(source[start:stop].rstrip())))
    return rows

def census(root=ROOT):
    files = []
    rows = []
    for p in sorted((root/FAMILY).glob("*.lean")):
        path = p.relative_to(root).as_posix()
        source = p.read_text()
        files.append(dict(path=path, sha256=digest(source), bytes=len(source.encode())))
        rows.extend(declarations(source,path))
    return dict(format=2, base=BASE, family=FAMILY,
        policy="All declarations; candidate cases include private control helpers; no semantic exclusions.",
        files=files, declarations=rows,
        totals=dict(files=len(files), declarations=len(rows),
            control_files=sum(Path(f["path"]).stem.endswith("Controls") for f in files),
            candidate_cases=sum(r["candidate_case"] for r in rows)))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--output", type=Path, required=True,
        help="Full inventory path outside the repository (H44)")
    args=parser.parse_args()
    if args.output.resolve().is_relative_to(ROOT):
        parser.error("bulk output must remain outside git (H44)")
    result=census()
    rendered=json.dumps(result,ensure_ascii=False,indent=2)+"\n"
    pins=dict(format=2,base=BASE, totals=result["totals"], files=result["files"],
              inventory_sha256=digest(rendered))
    manifest=json.dumps(pins,ensure_ascii=False,indent=2)+"\n"
    if args.write: DEST.write_text(manifest)
    elif DEST.read_text()!=manifest: raise SystemExit("FAIL: frozen census drift")
    args.output.write_text(rendered)
    print(json.dumps(result["totals"],sort_keys=True))
    print("inventory_sha256="+digest(rendered))
    print("CENSUS_TEXT_PINS_PASS (source identity only; no Lean proof claim)")

if __name__=="__main__": main()
