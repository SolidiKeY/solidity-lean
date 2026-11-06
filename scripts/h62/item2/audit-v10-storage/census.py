#!/usr/bin/env python3
"""Conservative source census. Not a Lean elaboration or satisfiability proof.
Every theorem/lemma command is retained, including controls and private helpers.
Raw signatures and lexical context are evidence; semantic classification remains
pending until checked by Lean. Bulk outputs must be written outside Git.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
OWNER = "V10 (v07-v11/v10-storage-operations)"

def sha(data):
    return hashlib.sha256(data).hexdigest()

def mask(text):
    # Keep newlines and offsets, erase nested comments, strings. Character-literal syntax is not interpreted.
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i] = " "
                if i+1 < len(text): out[i+1] = " "
                i += 2
            elif text[i] == '"':
                out[i] = " "; string = False; i += 1
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0: j = len(text)
            out[i:j] = " " * (j-i); i = j
        elif text[i] == '"':
            out[i] = " "; string = True; i += 1
        else:
            i += 1
    if depth or string: raise ValueError("unterminated comment/string")
    return "".join(out)

COMMAND = re.compile(r"(?m)^[ \t]*(?:(?:@\[[^\n]*\]|private|protected|noncomputable|unsafe)\s+)*(theorem|lemma)\s+([^\s(:{]+)")

def signature_end(code, start):
    depth = 0
    pending_let = 0
    has_match = False
    tokens = r"[(){}\[\]]|:=|\blet\b|\bhave\b|\bmatch\b|\bwhere\b|(?m:^[ \t]*\|)"
    for m in re.finditer(tokens, code[start:]):
        token = m.group().strip()
        if token in ("(", "{", "["): depth += 1
        elif token in (")", "}", "]"): depth -= 1
        elif depth == 0:
            if token == "match": has_match = True
            elif token == "|" and has_match: continue
            elif token in ("let", "have"): pending_let += 1
            elif token == ":=" and pending_let: pending_let -= 1
            else: return start + m.start()
    raise ValueError("declaration has no proof delimiter")

def frozen(root, relative):
    raw = (root / relative).read_bytes()
    expected = subprocess.check_output(["git", "show", f"{BASE}:{relative}"], cwd=root)
    if raw != expected: raise ValueError(f"frozen input changed: {relative}")
    return raw

def collect(root):
    area = root / "docs/module-map/v10-storage.md"
    text = frozen(root, "docs/module-map/v10-storage.md").decode()
    explicit = set(re.findall(r"`((?:Backend|Lowering)/[^` ,*]+\.lean)`", text))
    if "Other `Backend/StorageOps/*.lean`" not in text:
        raise ValueError("wildcard row changed; review scope expansion")
    backend = subprocess.check_output(["git", "ls-tree", "--name-only", BASE + ":Solidity/Backend/StorageOps"], cwd=root, text=True).splitlines()
    paths = explicit | {"Backend/StorageOps/" + name for name in backend if name.endswith(".lean")}
    files, declarations = [], []
    for relative in sorted(paths):
        path = root / "Solidity" / relative
        raw = frozen(root, str(path.relative_to(root))); source = raw.decode(); code = mask(source)
        files.append({"path": str(path.relative_to(root)), "sha256": sha(raw), "owner": OWNER, "scope": "explicit" if relative in explicit else "wildcard"})
        for m in COMMAND.finditer(code):
            end = signature_end(code, m.end())
            signature = source[m.start():end].strip()
            line = source.count("\n", 0, m.start()) + 1
            # Preserve entire source prefix to capture namespace, section,
            # implicit variables, local notation and options without guessing.
            declarations.append({"id": f"Solidity/{relative}:{line}:{m.group(2)}", "path": f"Solidity/{relative}", "line": line,
              "source_name": m.group(2), "kind": m.group(1), "signature": signature,
              "signature_sha256": sha(signature.encode()), "context_sha256": sha(raw[:len(source[:m.start()].encode())]),
              "owner": OWNER, "hypothesis_classification": "pending-elaboration", "witness": None,
              "status": "uncovered", "private": bool(re.search(r"\bprivate\b", code[m.start():m.end()])),
              "fully_qualified_name": None})
    ids = [d["id"] for d in declarations]
    if len(ids) != len(set(ids)): raise ValueError("duplicate statement id")
    return {"schema": 1, "base": BASE, "module_map_sha256": sha(area.read_bytes()),
      "scope_rule": "explicit module-map paths plus its Backend/StorageOps/*.lean wildcard; include controls/private declarations conservatively",
      "proof_boundary": "Source lexer only; not elaborated signatures, semantic premise classification, theorem census completeness proof, or witnesses",
      "files": files, "declarations": declarations,
      "counts": {"files": len(files), "declarations": len(declarations), "uncovered": len(declarations)}}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    args = parser.parse_args()
    root = pathlib.Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    output = args.output.resolve()
    if output == root or root in output.parents: parser.error("bulk output must be outside checkout")
    result = collect(root)
    output.mkdir(parents=True, exist_ok=True)
    (output / "census.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result["counts"], sort_keys=True))

if __name__ == "__main__": main()
