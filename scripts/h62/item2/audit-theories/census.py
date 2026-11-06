#!/usr/bin/env python3
"""Conservative frozen-source census. Source headers are NOT elaborated signatures.

Include every theorem/lemma in the mapped files, even unconditional/private ones;
never guess which binders elaborate to Prop. All records start uncovered.
Comments, strings, equation syntax and namespace/section nesting are handled.
Run with --out ABSOLUTE_OFF_GIT_DIRECTORY. Bulk evidence stays outside Git.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
ROOT = Path(__file__).resolve().parents[4]
MAP = "docs/module-map/theories.md"

def module_to_path(name):
    """Lean quoted name components may contain dots; split only outside «…»."""
    parts=re.findall(r"«[^»]+»|[^.«»]+",name)
    if not parts or ".".join(parts)!=name:
        raise ValueError("Unsupported Lean module name: "+name)
    components=[part[1:-1] if part.startswith("«") else part for part in parts]
    if any("/" in part or "\\" in part or part in (".","..") for part in components):
        raise ValueError("Non-local Lean module path: "+name)
    return Path(*components[:-1],components[-1]+".lean")

def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()

def mask(s):
    # Keep offsets/newlines; ignore nested comments and quoted string contents.
    out = list(s)
    i, depth, string = 0, 0, False
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
            if s[i] == '"': string = False
            if s[i] != "\n": out[i] = " "
            i += 1; continue
        if s.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2; continue
        if s.startswith("--", i):
            j = s.find("\n", i)
            if j == -1: j = len(s)
            out[i:j] = " " * (j-i); i = j; continue
        if s[i] == '"': string = True; out[i] = " "
        i += 1
    if depth or string: raise ValueError("Unterminated comment/string")
    return "".join(out)

def header_end(m, start):
    depth = 0
    pending_let = False
    for i in range(start, len(m)):
        ch = m[i]
        if depth == 0 and re.match(r"let\b", m[i:]) and (i == 0 or not (m[i-1].isalnum() or m[i-1] == "_")):
            pending_let = True
        if depth == 0 and re.match(r"where\b", m[i:]) and (i == 0 or not (m[i-1].isalnum() or m[i-1] == "_")):
            return i
        if depth == 0 and m.startswith(":=", i):
            if pending_let: pending_let = False
            else: return i
        if depth == 0 and ch == "|" and not m[m.rfind("\n", 0, i)+1:i].strip(): return i
        if ch in "({[": depth += 1
        elif ch in ")}]": depth -= 1
    raise ValueError("Declaration has no supported proof delimiter")

def producer(path):
    for family,lane,citation in (
        ("Mutability/","VS2","docs/feature-work/semantics-extensions.md:68,79"),
        ("Progress/","VS3","docs/feature-work/semantics-extensions.md:69,442"),
        ("CallerModel/","VC2","docs/feature-work/calculus-modes.md:35,135"),
        ("Reachable/","VC3","docs/feature-work/calculus-modes.md:36,44")):
        if path.startswith("Solidity/Theory/"+family):
            return {"lane":lane,"evidence":citation,"live_confirmation":"pending"}
    return {"lane":None,"evidence":"No proving assignment found; authorship is not ownership","live_confirmation":"pending"}

def scan(source, path):
    m = mask(source)
    events = re.compile(r"^([ \t]*)(?:(private|protected)\s+)?(theorem|lemma)\s+([^\s:({]+)|^(namespace|section|end|mutual)(?:[ \t]+([^\n]+))?", re.M)
    scopes, result, consumed = [], [], set()
    for e in events.finditer(m):
        if e[3]:
            consumed.add(e.start(3))
            end = header_end(m, e.end())
            namespace = ".".join(name for kind,name in scopes if kind == "namespace")
            name = e[4]
            qualified = name.removeprefix("_root_.") if name.startswith("_root_.") else ".".join(x for x in (namespace,name) if x)
            signature = source[e.start():end].strip()
            result.append({"source_name": qualified, "visibility": e[2] or "public", "kind": e[3],
                "file": path, "line": source.count("\n",0,e.start())+1,
                "source_header": signature, "source_header_sha256": sha(signature),
                "source_prefix_sha256": sha(source[:e.start()]),
                "status": "uncovered", "elaborated_signature": None,
                "hypothesis_classification": "pending Lean elaboration and manual review",
                "simultaneous_witness": None, "proving_owner": "unresolved; coordinator relay required",
                "documented_producing_lane": producer(path),
                "migration_overlay_owner": "solidity-h62-6-20261106/migrate-theory (no live owner transfer)"})
        else:
            kind, name = e[5], (e[6] or "").strip()
            if kind == "end":
                if not scopes: raise ValueError(f"Unmatched end in {path}")
                scopes.pop()
            else: scopes.append((kind,name))
    for token in re.finditer(r"\b(?:theorem|lemma)\s+", m):
        if token.start() not in consumed:
            raise ValueError(f"Unsupported declaration prefix at {path}:{m.count(chr(10),0,token.start())+1}")
    if scopes: raise ValueError(f"Unclosed scopes in {path}: {scopes}")
    names=[x["source_name"] for x in result]
    if len(names) != len(set(names)): raise ValueError(f"Duplicate names in {path}")
    return result

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args()
    out=a.out.resolve()
    if out.is_relative_to(ROOT): raise SystemExit("Bulk evidence must be outside checkout")
    subprocess.run(["git","merge-base","--is-ancestor",BASE,"HEAD"],cwd=ROOT,check=True)
    text=(ROOT/MAP).read_text()
    frozen_map=subprocess.check_output(["git","show",BASE+":"+MAP],cwd=ROOT).decode()
    if text != frozen_map: raise SystemExit("Frozen module map changed: "+MAP)
    files=re.findall(r"^\| `(Theory/[^`]+\.lean)`",text,re.M)
    if not files or len(files)!=len(set(files)): raise SystemExit("Empty or duplicate module-map rows")
    records=[]; inputs={MAP:sha(text)}; modules=[]
    for f in files:
        path="Solidity/"+f
        source=(ROOT/path).read_text()
        frozen=subprocess.check_output(["git","show",BASE+":"+path],cwd=ROOT).decode()
        if source != frozen: raise SystemExit("Frozen source changed: "+path)
        inputs[path]=sha(source)
        rows=scan(source,path); records.extend(rows)
        modules.append({"file":path,"theorems":len(rows)})
    names=[x["source_name"] for x in records]
    if len(names)!=len(set(names)): raise SystemExit("Cross-module duplicate source names")
    report={"base":BASE,"module_map":MAP,"modules":modules,"source_inputs_sha256":inputs,
      "declarations":records,"counts":{"modules":len(files),"theorems":len(records),
      "covered":0,"uncovered":len(records)},"limitations":[
      "Lexical source census; names require elaboration confirmation (open namespaces may resolve dotted names).",
      "All declarations retained; Prop binders and inherited variables require elaborated census.",
      "Not a proof of hypotheses, statement fidelity or compiler success."]}
    out.mkdir(parents=True,exist_ok=True)
    payload=json.dumps(report,ensure_ascii=False,indent=2)+"\n"
    (out/"census.json").write_text(payload)
    (out/"census.sha256").write_text(sha(payload)+"  census.json\n")
    print(json.dumps(report["counts"],sort_keys=True))

if __name__ == "__main__": main()
