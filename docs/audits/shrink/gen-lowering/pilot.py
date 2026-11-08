#!/usr/bin/env python3
"""Reproduce the G19 anti-unification pilot; logs belong outside Git."""
import argparse, hashlib, json, os, pathlib, re, subprocess, time
BASE = "381328f608032dd19c405373c2b265e83a969850"
ROOT = pathlib.Path(__file__).resolve().parents[4]
FAMILY = "Solidity/Lowering/G19"
def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True)
def sources(base=False):
    names = git("ls-tree", "-r", "--name-only", BASE, FAMILY).splitlines()
    return {n: git("show", BASE+":"+n) if base else (ROOT/n).read_text() for n in names if n.endswith(".lean")}
def inventory(src):
    exports=[]; decls=0; proof_lines=0
    for path,text in sorted(src.items()):
        ns=""
        for m in re.finditer(r"(?m)^(namespace|end|theorem|lemma|def|abbrev|structure|inductive)\b[^\n]*",text):
            kind=m.group(1)
            if kind in ("namespace","end"): continue
            decls+=1
            if kind not in ("theorem","lemma"): continue
            name=m.group(0).split()[1]
            stop=text.index(":=",m.start())
            header=text[m.start():stop].strip()
            exports.append({"file":path,"name":name,"header":header,"sha256":hashlib.sha256(header.encode()).hexdigest()})
            body=text[stop:].split("\n\n",1)[0]
            proof_lines+=len(body.splitlines())
    return {"physical_lines":sum(len(t.splitlines()) for t in src.values()),"declarations":decls,"theorems":len(exports),"proof_body_lines_to_blank_separator":proof_lines,"exports":exports}
def measure(out):
    out.mkdir(parents=True,exist_ok=True)
    os.environ["LEAN_NUM_THREADS"]="1"
    os.environ["LAKE_CACHE_DIR"]=subprocess.check_output(["lean","--print-prefix"],text=True).strip()+"/lake/cache"
    with (out/"warmup.log").open("w") as log:
        subprocess.run(["lake","build","Solidity.KeySort"]+[n[:-5].replace("/",".") for n in sources()],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
        subprocess.run(["python3","scripts/ci/restore-lake-artifacts.py"],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    rows=[]
    for n in sources():
        cmd=["lake","env","lean","-j1","-M8192","--tstack=131072",n]
        start=time.monotonic()
        with (out/(pathlib.Path(n).stem+".log")).open("w") as log:
            p=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
        rows.append({"file":n,"command":cmd,"exit":p.returncode,"seconds":time.monotonic()-start})
        print(n,rows[-1]["exit"],round(rows[-1]["seconds"],3),flush=True)
        if p.returncode: break
    result={"source_sha256":{n:hashlib.sha256(t.encode()).hexdigest() for n,t in sources().items()},"git_status":git("status","--porcelain"),"lean_version":subprocess.check_output(["lean","--version"],text=True).strip(),"lake_version":subprocess.check_output(["lake","--version"],text=True).strip(),"head":git("rev-parse","HEAD").strip(),"serial":True,"threads":1,"memory_mib":8192,"systemd_scope":False,"method":"Fresh per-file elaboration including kernel checking; imports prebuilt and shared. Not isolated kernel-only timing.","rows":rows,"seconds":sum(r["seconds"] for r in rows),"complete":len(rows)==len(sources()) and all(r["exit"]==0 for r in rows)}
    (out/"timing.json").write_text(json.dumps(result,indent=2)+"\n")
    if not result["complete"]: raise SystemExit(1)
def main():
    a=argparse.ArgumentParser(); a.add_argument("mode",choices=["inventory","measure","compare"]);a.add_argument("output",type=pathlib.Path);a.add_argument("--base",action="store_true");v=a.parse_args()
    if v.mode=="measure": measure(v.output)
    elif v.mode=="compare":
        before=inventory(sources(True)); after=inventory(sources())
        old={(x["file"],x["name"]):x["header"] for x in before["exports"]}
        new={(x["file"],x["name"]):x["header"] for x in after["exports"]}
        if len(old)!=len(before["exports"]) or len(new)!=len(after["exports"]): raise SystemExit("ambiguous export keys")
        changed=[list(k) for k,h in old.items() if new.get(k)!=h]
        result={"preserved":not changed,"original_count":len(old),"changed_or_missing":changed,"added":[list(k) for k in new.keys()-old.keys()]}
        v.output.write_text(json.dumps(result,indent=2)+"\n")
        if changed: raise SystemExit(1)
    else: v.output.write_text(json.dumps(inventory(sources(v.base)),indent=2)+"\n")
if __name__=="__main__":main()
