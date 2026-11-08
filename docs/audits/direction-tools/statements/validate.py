#!/usr/bin/env python3
"""Offline checker for audit artifacts; --remote additionally verifies pinned excerpts.
Run: python3 -I docs/audits/direction-tools/statements/validate.py [--remote]
"""
import csv,hashlib,json,pathlib,subprocess,sys,urllib.request,re
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
BASE="d4ad633a9624263a59b14fd2c520b9bc602f88f3"
def git(*a):return subprocess.check_output(["git",*a],cwd=ROOT,text=True).strip()
def cite(c):
    path,_,needle=c.partition("#")
    assert (ROOT/path).is_file(),c
    if needle:assert needle in (ROOT/path).read_text(),c

def main():
    subprocess.run([sys.executable,"-I",str(HERE/"scan.py"),"--check"],cwd=ROOT,check=True)
    rows=list(csv.DictReader((HERE/"statements.csv").open()))
    summary=json.loads((HERE/"summary.json").read_text())
    refs=json.loads((HERE/"references.json").read_text())
    assert len({(r["path"],r["line"]) for r in rows})==len(rows)
    assert sum("top30_imported_module" in r["selection"] for r in rows)==30
    for r in rows:
        cite(r["path"]+"#"+r["name"])
        if r["witness"]:cite(r["witness"])
        assert r["strength"] in ("strong","weaker than named","trivial","unclear")
        assert r["english_claim"] and r["comparison"] and r["witness_needed"]
    for p in summary["top_problems"]:cite(p["source"])
    # Every measured Lean source is pinned; ignore the audit output itself.
    for path in git("ls-files","*.lean").splitlines():
        assert git("hash-object",path)==git("rev-parse",BASE+":"+path),path
    changed=git("diff","--name-only",BASE).splitlines()
    assert all(p.startswith("docs/audits/direction-tools/statements/") for p in changed),changed
    for p in HERE.iterdir():
        if p.is_file():assert p.stat().st_size<1000000,p
    if "--remote" in sys.argv:
        for r in refs:
            raw=urllib.request.urlopen(r["url"],timeout=30).read();text=raw.decode()
            assert hashlib.sha256(raw).hexdigest()==r["source_sha256"]
            assert r["statement"] in text
            assert text[:text.index(r["statement"])].count("\n")+1==r["line"]
            print("PINNED_REFERENCE_PASS",r["id"],r["theorem"])
    print("AUDIT_VALIDATION_PASS",len(rows),"statements; source witnesses checked as text, not elaborated")
if __name__=="__main__":main()
