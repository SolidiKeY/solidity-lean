#!/usr/bin/env python3
"""Conservative source census. Not an elaborator or a witness-coverage certificate.

Output is deliberately off git. Every named theorem is retained, including
unconditional ones; deciding implicit/section premises needs kernel inspection.
Structure source regions are retained because signature-only interfaces use
records rather than theorem commands; field extraction remains pending. No source row is called witnessed.
"""
import argparse
import glob
import hashlib
import json
import pathlib
import re

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def digest(s):
    return hashlib.sha256(s.encode()).hexdigest()

def mask(s):
    # Preserve offsets/newlines while removing nested comments and string bodies.
    out = list(s)
    i = 0
    depth = 0
    string = False
    while i < len(s):
        if depth:
            if s.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2; continue
            if s.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2; continue
            if s[i] != "\n": out[i] = " "
            i += 1; continue
        if string:
            if s[i] == "\\":
                out[i] = " "
                if i+1 < len(s): out[i+1] = " "
                i += 2; continue
            if s[i] == chr(34): string = False
            if s[i] != "\n": out[i] = " "
            i += 1; continue
        if s.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2; continue
        if s.startswith("--", i):
            end = s.find("\n", i)
            if end < 0: end = len(s)
            out[i:end] = " " * (end-i); i = end; continue
        if s[i] == chr(34): string = True; out[i] = " "
        i += 1
    if depth or string: raise ValueError("Unclosed comment/string")
    return "".join(out)

def modules(root):
    source = root / "docs/module-map/memory-operations.md"
    found, missing = set(), []
    for line in source.read_text().splitlines():
        if not line.startswith("| `"): continue
        for pattern in re.findall(r"`([^`]*\.lean)`", line.split("|")[1]):
            variants = [pattern]
            while any("{" in v for v in variants):
                new = []
                for v in variants:
                    m = re.search(r"\{([^}]+)\}", v)
                    new.extend([v[:m.start()]+part+v[m.end():] for part in m[1].split(",")] if m else [v])
                variants = new
            for v in variants:
                if not v.startswith("Solidity/"): v = "Solidity/"+v
                matches = glob.glob(str(root / v))
                if not matches: missing.append(v)
                found.update(pathlib.Path(f).relative_to(root).as_posix() for f in matches)
    return source, sorted(found), sorted(set(missing))

def scan(root, path):
    text = (root/path).read_text()
    clean = mask(text)
    rows, scopes = [], []
    commands = list(re.finditer(r"^[ \t]*(?:(?:private|protected|noncomputable|unsafe)\s+)*(namespace|section|end|theorem|lemma|structure|class|axiom|def|abbrev|opaque|inductive|instance|example|variable|universe|open|export|attribute|set_option|syntax|macro_rules|macro|elab|notation|infixl|infixr|prefix|postfix|initialize|mutual|import)\b(?:[ \t]+([^\s:(\[{]+))?", clean, re.M))
    for n, m in enumerate(commands):
        kind, name = m[1], m[2]
        if kind in ("namespace", "section"):
            scopes.append((kind, name or "")); continue
        if kind == "end":
            if scopes: scopes.pop()
            continue
        if kind not in ("theorem", "lemma", "structure", "class", "axiom"): continue
        if not name: raise ValueError(f"Unnamed {kind} in {path}")
        limit = commands[n+1].start() if n+1 < len(commands) else len(text)
        # Retain the full command region; lexical := splitting cannot distinguish
        # conclusion-local lets from the proof delimiter. Only elaboration can
        # certify the frozen signature (including implicit and section binders).
        region = text[m.start():limit]
        namespace = ".".join(v for k,v in scopes if k == "namespace")
        fqn = (namespace+"." if namespace else "")+name
        rows.append(dict(kind=kind, name=fqn, path=path, line=text.count("\n",0,m.start())+1,
                         source_command_region=region, source_region_sha256=digest(region),
                         source_start=m.start(), source_end=limit,
                         name_kind="source-qualified spelling; not a kernel FQN",
                         visibility="private" if re.search(r"\bprivate\b",clean[m.start():m.start(1)]) else "public-or-protected",
                         status="unverified", signature_status="pending kernel elaboration", scope="interface-named-file" if "Interface" in path else "mapped-module",
                         owner_status="pending exact producer attribution",
                         premise_status="pending elaboration including implicit and section binders"))
        if kind in ("structure", "class"):
            # Retain whole source declaration: field parsing is deferred, never dropped.
            rows[-1]["field_status"] = "pending exact field census and simultaneous witness"
    return rows

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
    parser.add_argument("--output", type=pathlib.Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    source, paths, missing = modules(root)
    declarations = [r for path in paths for r in scan(root,path)]
    identities = [(r["path"], r["line"], r["name"]) for r in declarations]
    if len(identities) != len(set(identities)): raise ValueError("Duplicate source identity")
    result = dict(base=BASE, map=str(source.relative_to(root)), map_sha256=digest(source.read_text()),
        modules=[dict(path=p,sha256=digest((root/p).read_text())) for p in paths],
        missing_modules=missing, declarations=declarations,
        boundary="Source-only conservative superset. No kernel signature fidelity, owner, witness or totality claim.",
        counts=dict(modules=len(paths), declarations=len(declarations),
                    theorems=sum(r["kind"] in ("theorem","lemma") for r in declarations),
                    structures=sum(r["kind"] in ("structure","class") for r in declarations),
                    verified_witnesses=0))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print(json.dumps(dict(counts=result["counts"],missing_modules=missing,sha256=hashlib.sha256(args.output.read_bytes()).hexdigest())))
    return 1 if missing else 0

if __name__ == "__main__":
    raise SystemExit(main())
