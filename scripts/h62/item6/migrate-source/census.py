#!/usr/bin/env python3
"""Deterministic source/import census. Lexical inventory is not elaborated API proof."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def mask(text):
    """Mask nested comments and strings, preserving newlines and offsets."""
    out = list(text)
    i, depth, string = 0, 0, False
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
                out[i] = " "; i += 1
                if i < len(text):
                    if text[i] != "\n": out[i] = " "
                    i += 1
            else:
                if text[i] == '"': string = False
                if text[i] != "\n": out[i] = " "
                i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1: j = len(text)
            out[i:j] = " " * (j-i); i = j
        elif text.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2
        elif text[i] == '"':
            out[i] = " "; string = True; i += 1
        else: i += 1
    return "".join(out)

def imports(text):
    return [m for line in mask(text).splitlines()
            if re.match(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+", line)
            for m in re.sub(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+", "", line).split()]

def sha(data): return hashlib.sha256(data).hexdigest()

def select_assigned(modules, assigned_paths=None):
    if assigned_paths is None:
        return sorted(m for m, p in modules.items() if p.startswith("Solidity/Source/"))
    paths = list(assigned_paths)
    if not paths or len(set(paths)) != len(paths):
        raise ValueError("assigned scope must contain unique nonempty paths")
    if any(not p.startswith("Solidity/Source/") or not p.endswith(".lean")
           or ".." in Path(p).parts for p in paths):
        raise ValueError("assigned scope contains a non-Source Lean path")
    available = {p: m for m, p in modules.items()}
    missing = sorted(set(paths) - available.keys())
    if missing:
        raise ValueError("assigned paths missing at requested revision: " + ", ".join(missing))
    return sorted(available[p] for p in paths)


def census(root, revision=BASE, assigned_paths=None):
    def git(*args):
        return subprocess.check_output(["git", "-C", str(root), *args])
    revision = git("rev-parse", "--verify", revision + "^{commit}").decode().strip()
    paths = sorted(p for p in git("ls-tree", "-r", "--name-only", revision).decode().splitlines() if p.endswith(".lean"))
    blobs = {p: git("show", f"{revision}:{p}") for p in paths}
    modules = {p[:-5].replace("/", "."): p for p in paths}
    graph = {m: imports(blobs[p].decode()) for m, p in modules.items()}
    assigned = select_assigned(modules, assigned_paths)
    closure, order, visiting = set(), [], set()
    def visit(m):
        if m in visiting: raise ValueError("import cycle at " + m)
        if m in closure or m not in modules: return
        visiting.add(m)
        for dep in graph[m]: visit(dep)
        visiting.remove(m); closure.add(m); order.append(m)
    visit("Solidity.KeySort")
    for m in assigned: visit(m)
    entries = []
    declaration = re.compile(r"\b(theorem|lemma|def|abbrev|inductive|structure|class|instance|example|axiom|opaque)\b")
    for m in assigned:
        p = modules[m]; data = blobs[p]; text = data.decode(); clean = mask(text)
        candidates = [{"line": i, "kind": hit.group(1), "text": line.strip()}
                      for i,line in enumerate(clean.splitlines(), 1)
                      if (hit := declaration.search(line))]
        entries.append({"module": m, "path": p, "sha256": sha(data), "imports": graph[m],
                        "lexical_declaration_candidates": candidates,
                        "budget_options": [line.strip() for line in clean.splitlines() if re.search(r"set_option\s+(maxHeartbeats|maxRecDepth)",line)],
                        "sorry_tokens": len(re.findall(r"\bsorry\b", clean)),
                        "axiom_tokens": len(re.findall(r"\baxiom\b", clean)),
                        "native_decide_tokens": len(re.findall(r"\bnative_decide\b", clean))})
    direct = sorted({d for m in assigned for d in graph[m] if d not in assigned})
    reverse = sorted((m,d) for m in graph if m not in assigned for d in graph[m] if d in assigned)
    return {"schema": 1, "base": BASE, "revision": revision,
            "boundary": "Exact file hashes freeze all bytes, including statements and proof budgets. Lexical candidates are navigational, not elaborated declarations or API equivalence.",
            "assigned_count":len(assigned), "closure_count":len(closure), "files": entries,
            "scope_selection": "explicit frozen paths" if assigned_paths is not None else "all Source paths at revision",
            "unassigned_source_paths": sorted(p for m,p in modules.items() if p.startswith("Solidity/Source/") and m not in assigned),
            "external_direct_imports": direct, "nonlocal_imports": sorted({d for m in closure for d in graph[m] if d not in modules}), "external_transitive_local_modules":sorted(closure-set(assigned)),
            "external_consumers":reverse, "serial_build_order":order,
            "closure_file_hashes": {modules[m]:sha(blobs[modules[m]]) for m in sorted(closure)}}

if __name__ == "__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("--root", type=Path, default=Path.cwd()); ap.add_argument("--revision",default=BASE); ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--scope-manifest", type=Path, help="Retain explicit original paths when inspecting a newer revision")
    ap.add_argument("--prior-census", type=Path, help="Record lexical/file drift against an immutable earlier census; not an API verdict")
    a=ap.parse_args()
    paths=None
    if a.scope_manifest:
        scope=json.loads(a.scope_manifest.read_text())
        if scope["base"] != BASE:
            raise ValueError("scope manifest differs from original pinned base")
        paths=[r["path"] for r in scope["original_files"]]
        canonical=subprocess.check_output(["git", "-C", str(a.root), "ls-tree", "-r", "--name-only", BASE, "Solidity/Source"], text=True).splitlines()
        canonical={p for p in canonical if p.endswith(".lean")}
        if len(paths) != len(set(paths)) or set(paths) != canonical:
            raise ValueError("scope manifest must equal the exact original Source path set")
    result=census(a.root,a.revision,paths)
    if a.scope_manifest:
        result["scope_manifest_sha256"]=sha(a.scope_manifest.read_bytes())
        result["scope_matches_original_base"]=True
    if a.prior_census:
        prior=json.loads(a.prior_census.read_text())
        before={r["path"]:r for r in prior["files"]}
        after={r["path"]:r for r in result["files"]}
        if prior["base"] != BASE or before.keys() != after.keys():
            raise ValueError("prior census must have same original base and exact assigned path set")
        drift=[]
        for path in sorted(before):
            old,new=before[path],after[path]
            drift.append({"path":path, "old_sha256":old["sha256"], "new_sha256":new["sha256"],
                          "changed":old["sha256"] != new["sha256"],
                          "imports_added":sorted(set(new["imports"])-set(old["imports"])),
                          "imports_removed":sorted(set(old["imports"])-set(new["imports"])),
                          "old_lexical_candidates":len(old["lexical_declaration_candidates"]),
                          "new_lexical_candidates":len(new["lexical_declaration_candidates"]),
                          "old_budget_options":old["budget_options"], "new_budget_options":new["budget_options"]})
        result["prior_census_sha256"]=sha(a.prior_census.read_bytes())
        result["frozen_scope_drift"]=drift
        result["drift_boundary"]="Inherited source/lexical drift only; not elaborated API equivalence, owner permission, proof validation or attribution to this lane."
    a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:result[k] for k in ("base","assigned_count","closure_count","external_direct_imports")}))
