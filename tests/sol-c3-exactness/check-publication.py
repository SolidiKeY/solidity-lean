#!/usr/bin/env python3
"""Read-only exact publication/delta audit; does not run Lean or certify master gates."""
import argparse,copy,hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
AREA=ROOT/"tests/sol-c3-exactness"
PUBLISHED="89373e34cdfd6bb5db7054b1c204d01edffc5fa7"
CHECKPOINT="a7f4755cc1bd375052622aec6a966b6a1c21e427"
BASE="6f3eedf0788ee1f8a3bcf230558c712ecdca04d5"
EXPECTED={"Solidity/Frontend/C3Exactness/"+n+".lean" for n in ["Admission","Controls","Linearization","Trace"]}
SCOPE=["Solidity/Frontend/C3Exactness","tests/sol-c3-exactness","scripts/check-sol-c3-exactness.py","docs/feature-work/c3-exactness.md"]
def sha(b):return hashlib.sha256(b).hexdigest()
def require(ok,message):
    if not ok:raise ValueError(message)
def git(*args):
    try:return subprocess.check_output(["git",*args],cwd=ROOT,stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError as e:raise ValueError("Git object/ancestry check failed") from e

def validate(r):
    require(r.get("published_master")==PUBLISHED and r.get("owned_checkpoint")==CHECKPOINT and r.get("base")==BASE,"revision pin drift")
    require(r.get("repository")==str(ROOT),"repository drift")
    require(r.get("previous_published_master")=="b419c3cf4f642ae519b66bebc26cdf2f7cf93574","previous publication pin drift")
    require(git("branch","--show-current").decode().strip()=="codex/solidity-sol2-20261104/c3-exactness","assigned branch drift")
    for a,b in [(BASE,CHECKPOINT),(r.get("previous_published_master","missing"),PUBLISHED),(PUBLISHED,"origin/master"),(CHECKPOINT,"HEAD")]:
        git("merge-base","--is-ancestor",a,b)
    m=json.loads((AREA/"manifest.json").read_text())
    published=set(git("ls-tree","-r","--name-only",PUBLISHED,"--",SCOPE[0]).decode().splitlines())
    require(published==EXPECTED and sorted(published)==r.get("published_c3_modules"),"published module inventory drift")
    paths=published|set(m["source_pins"])
    actual={p:dict(owned_sha256=sha((ROOT/p).read_bytes()),published_sha256=sha(git("show",PUBLISHED+":"+p))) for p in paths}
    require(r.get("comparisons")==actual,"source comparison drift")
    for p,pin in m["source_pins"].items():
        require(actual[p]["owned_sha256"]==pin==actual[p]["published_sha256"]==sha(git("show",BASE+":"+p)),"producer/base pin drift")
    for p in m["modules"]:
        require((ROOT/p).read_bytes()==git("show",CHECKPOINT+":"+p),"owned proof changed since reviewed checkpoint")
    changed=sorted(p for p in published if actual[p]["owned_sha256"]!=actual[p]["published_sha256"])
    identical=sorted(published-set(changed))
    require(changed==r.get("changed_published_modules")==[SCOPE[0]+"/Controls.lean"],"published delta drift")
    require(identical==r.get("identical_published_modules"),"identity inventory drift")
    require(git("show",PUBLISHED+":"+SCOPE[0]+"/Controls.lean")==git("show","dc6b974c7e5313a22a6e43dcc98df3303f826aa5:"+SCOPE[0]+"/Controls.lean"),"published Controls reviewed pin drift")
    require(sorted(set(m["modules"])-published)==r.get("remaining_new_modules"),"remaining module inventory drift")
    patch=Path(r.get("proof_checkpoint_scope_patch","missing")).resolve()
    require(patch.is_relative_to(AREA/".artifacts") and patch.is_file(),"patch location drift")
    expected=git("diff","--binary",PUBLISHED,CHECKPOINT,"--",*SCOPE)
    require(patch.read_bytes()==expected and sha(expected)==r.get("proof_checkpoint_scope_patch_sha256"),"exact remaining patch drift")
    return actual

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--self-test",action="store_true");args=ap.parse_args()
    path=AREA/"evidence/published-master-89373e34.json";r=json.loads(path.read_text());actual=validate(r)
    rejected=0
    if args.self_test:
        bads=[]
        for key,value in [("published_master",BASE),("owned_checkpoint",BASE),("repository","/wrong"),("previous_published_master",BASE),("published_c3_modules",r["published_c3_modules"]+[r["published_c3_modules"][0]]),("published_c3_modules",[]),("comparisons",{}),("remaining_new_modules",[]),("changed_published_modules",[]),("identical_published_modules",[]),("proof_checkpoint_scope_patch_sha256","0"*64),("proof_checkpoint_scope_patch","/etc/passwd")]:
            bad=copy.deepcopy(r);bad[key]=value;bads.append(bad)
        for bad in bads:
            try:validate(bad)
            except ValueError:rejected+=1
            else:raise ValueError("negative control accepted")
    print(json.dumps(dict(result="PUBLICATION_EXACTNESS_PASS",published=PUBLISHED,owned_checkpoint=CHECKPOINT,remaining_new_modules=r["remaining_new_modules"],negative_controls_rejected=rejected,checker_sha256=sha(Path(__file__).read_bytes()),receipt_sha256=sha(path.read_bytes()),comparisons=actual,boundary="Read-only Git/source/delta audit only; no Lean rerun, no external master gate certification, no remaining lane gate waiver"),indent=2))
if __name__=="__main__":main()
