#!/usr/bin/env python3
"""Deterministic source census, not an elaborated API/axiom proof.

Whole-file hashes conservatively freeze every statement, body and option.
Comments and strings are masked before source-level import/declaration scans.
"""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def mask(text):
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2; continue
            if text.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2; continue
            if text[i] != "\n": out[i] = " "
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                out[i:i+2] = ["\n" if c == "\n" else " " for c in text[i:i+2]]; i += 2; continue
            if text[i] == '"': string = False
            if text[i] != "\n": out[i] = " "
        elif text.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2; continue
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end == -1: end = len(text)
            out[i:end] = " " * (end-i); i = end; continue
        elif text[i] == "'" and (char := re.match(r"'(?:\\.|[^'\\\n])'", text[i:])):
            size = len(char[0]); out[i:i+size] = " " * size; i += size; continue
        elif text[i] == '"':
            string = True; out[i] = " "
        i += 1
    return "".join(out)

def imports(text):
    return re.findall(r"(?m)^\s*(?:public\s+|private\s+)?import\s+([A-Za-z_][\w.]*)", mask(text))

def census(root):
    paths = sorted((root / "Solidity/Tools").glob("*.lean"))
    all_imports = {}
    for top in [root / "Solidity", root / "vendor/LeanTeX"]:
        for p in sorted(top.rglob("*.lean")):
            name = str(p.relative_to(root)).removesuffix(".lean").replace("/", ".")
            if name.startswith("vendor.LeanTeX."): name = name.removeprefix("vendor.LeanTeX.")
            all_imports[name] = imports(p.read_text())
    assigned = {"Solidity.Tools." + p.stem for p in paths}
    records = []
    for p in paths:
        raw = p.read_bytes(); source = raw.decode(); clean = mask(source)
        name = "Solidity.Tools." + p.stem
        closure, todo = set(), list(all_imports[name])
        while todo:
            dep = todo.pop()
            if dep in closure: continue
            closure.add(dep); todo.extend(all_imports.get(dep, []))
        declarations = []
        pattern = r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|unsafe|noncomputable|partial|nonrec)\s+)*(def|abbrev|theorem|lemma|structure|inductive|class|instance|opaque|axiom|syntax|macro_rules|macro|elab_rules|elab)\b([^\n]*)"
        for m in re.finditer(pattern, clean):
            declarations.append({"line": clean.count("\n", 0, m.start(1)) + 1, "kind": m[1], "source_head": m[2].strip()})
        records.append({"path": str(p.relative_to(root)), "module": name,
            "sha256": hashlib.sha256(raw).hexdigest(), "imports": all_imports[name],
            "outside_tools_imports": sorted(set(all_imports[name]) - assigned),
            "transitive_imports": sorted(closure),
            "declaration_candidates": declarations,
            "proof_budget_options": re.findall(r"(?m)^.*set_option.*(?:maxHeartbeats|maxRecDepth).*$", clean),
            "trust_tokens": {k: len(re.findall(r"\b" + k + r"\b", clean)) for k in ["sorry", "axiom", "native_decide"]}})
    return {"base": BASE, "boundary": "source-level candidates; whole-file hashes freeze all original bytes; not an elaborated API certificate", "module_count": len(records), "modules": records}

if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--root", type=Path, default=Path.cwd()); ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    subprocess.run(["git", "merge-base", "--is-ancestor", BASE, "HEAD"], cwd=args.root, check=True)
    args.output.write_text(json.dumps(census(args.root), indent=2, sort_keys=True) + "\n")
