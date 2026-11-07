#!/usr/bin/env python3
"""Conservative source census; whole-file hashes freeze all statements and cases.
Declaration markers are an index, not an elaborated Lean API hash.
"""
import argparse, hashlib, json, pathlib, re, subprocess
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
ROOT = pathlib.Path(__file__).resolve().parents[4]
def sha(b): return hashlib.sha256(b).hexdigest()
def validate_sources(manifest, root):
    expected={x["path"]:x["sha256"] for x in manifest["files"]}
    actual={str(f.relative_to(root)):sha(f.read_bytes()) for f in (root/"Solidity/Corpus").rglob("*.lean")}
    return dict(missing=sorted(expected.keys()-actual.keys()), unexpected=sorted(actual.keys()-expected.keys()),
                changed=sorted(f for f in expected.keys() & actual.keys() if expected[f]!=actual[f]))
def census():
    files = sorted(subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE, "Solidity/Corpus/"], cwd=ROOT, text=True).splitlines())
    modules = {}
    for f in subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE], cwd=ROOT, text=True).splitlines():
        if f.endswith(".lean"):
            raw = subprocess.check_output(["git", "show", f"{BASE}:{f}"], cwd=ROOT)
            modules[f[:-5].replace("/", ".")] = (f, raw)
    def imports(raw):
        return re.findall(r"^import ([\w.]+)", raw.decode(), re.M)
    visited = set()
    def visit(m):
        if m in visited or m not in modules: return
        visited.add(m)
        for dep in imports(modules[m][1]): visit(dep)
    rows=[]
    for f in files:
        raw=modules[f[:-5].replace("/", ".")][1]; text=raw.decode()
        visit(f[:-5].replace("/", "."))
        rows.append(dict(path=f, sha256=sha(raw), bytes=len(raw), imports=imports(raw),
            markers=[dict(line=i, text=s) for i,s in enumerate(text.splitlines(),1)
                     if re.match(r"^(?:private |protected |noncomputable )?(?:def |abbrev |theorem |lemma |example\b|macro |inductive |structure |class |instance\b|set_option |#guard|#eval|#print)",s)],
            unchanged=(ROOT/f).read_bytes()==raw))
    return dict(base=BASE, files=rows, closure=sorted(visited), external_dependencies=sorted(m for m in visited if not m.startswith("Solidity.Corpus.")),
                note="Source markers are conservative; exact raw file SHA256 freezes every byte, including unnamed examples, guards, programs and proof budgets. No elaborated API equivalence claim.")
if __name__ == "__main__":
    a=argparse.ArgumentParser(); a.add_argument("--output", type=pathlib.Path, required=True); args=a.parse_args()
    result=census(); args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(files=len(result["files"]), closure=len(result["closure"]), external_dependencies=len(result["external_dependencies"]), unchanged=all(x["unchanged"] for x in result["files"]))))
