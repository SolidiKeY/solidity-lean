#!/usr/bin/env python3
"""Replay the exact H70 owner relay into private evidence only. No Lean run.
Original Hash files remain READ ONLY; full owner migration gates remain pending.
"""
import difflib,hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
OWNER="2a18afcdba00a85645b0b3079704f78ffcd78860"
REL="Solidity/Hash/CollisionBound.lean"
EXPECTED_BASE="b54c93a5b24340a19160c1fb378d057ccee60f84"
EXPECTED_TARGET_BLOB="092971eda8c7d6997276a92ba19b25b7ce05844e"
EXPECTED_ADAPTIVE_BASE="cb5d5a1c61f7350aa01d9d0c81c8f4403b19fab3"
def blob(data):return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
def apply_relay(data):
    if blob(data)!=EXPECTED_BASE:raise ValueError("H70 exact base blob mismatch")
    text=data.decode()
    for a,b,count in [("if_true","ite_true",1),("if_pos","ite_eq_left",4),("if_neg","ite_eq_right",4)]:
        text,n=re.subn(r"\b"+a+r"\b",b,text)
        if n!=count:raise ValueError("owner relay token count mismatch: "+a)
    old="A.countP (fun a => (a == x) || t.contains a) := by\n      congr 1"
    if text.count(old)!=1:raise ValueError("owner relay hsplit anchor mismatch")
    text=text.replace(old,"A.countP (fun a => (a == x) || t.contains a) := by\n      simp only [List.contains_cons]")
    for name in ("Near","Covers"):
        old="    simp only [decide_eq_true_eq, "+name+"] at hn"
        if text.count(old)!=1:raise ValueError("owner relay decidable anchor mismatch")
        parameters="N L a b" if name=="Near" else "N L a r"
        text=text.replace(old,"    have hn' : "+name+" "+parameters+" := of_decide_eq_true hn\n    unfold "+name+" at hn'")
    result=text.encode()
    if blob(result)!=EXPECTED_TARGET_BLOB:raise ValueError("relayed owner target blob mismatch")
    return result

def main():
    out=Path(sys.argv[1]) if len(sys.argv)==2 else Path("/workspace/migrate-roadmap-evidence/h70/hash-owner-overlay")
    if not out.resolve().is_relative_to(Path("/workspace/migrate-roadmap-evidence/h70")):raise ValueError("private evidence destination required")
    before=(ROOT/REL).read_bytes()
    original=subprocess.check_output(["git","show",BASE+":"+REL],cwd=ROOT)
    if before!=original:raise ValueError("original checkout differs from published pinned base")
    adaptive=(ROOT/"Solidity/Hash/Adaptive.lean").read_bytes()
    if blob(adaptive)!=EXPECTED_ADAPTIVE_BASE:raise ValueError("Adaptive advertised base mismatch")
    after=apply_relay(before)
    target=out/REL;target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists() and target.read_bytes()!=after:raise ValueError("unexpected existing private overlay: preserve it")
    target.write_bytes(after)
    patch=''.join(difflib.unified_diff(before.decode().splitlines(keepends=True),after.decode().splitlines(keepends=True),fromfile="a/"+REL,tofile="b/"+REL))
    (out/"CollisionBound.owner.patch").write_text(patch)
    available=subprocess.run(["git","cat-file","-e",OWNER+"^{commit}"],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0
    if available:
        if subprocess.check_output(["git","show",OWNER+":"+REL],cwd=ROOT)!=after:raise ValueError("local owner commit differs from relayed payload")
    manifest=dict(owner_commit_as_relayed=OWNER,owner_commit_local_object_available=available,pinned_base=BASE,
        authorization="H70 reviewed owner relay; isolated migration use only. Routing gives no original-file edit permission.",
        original_path=str(ROOT/REL),private_overlay=str(target),base_blob=blob(before),target_blob=blob(after),
        overlay_sha256=hashlib.sha256(after).hexdigest(),patch_sha256=hashlib.sha256(patch.encode()).hexdigest(),
        adaptive_base_blob_verified=blob(adaptive),adaptive_staged=False,
        original_file_unchanged=(ROOT/REL).read_bytes()==before,
        runtime_validation="PENDING: further Lean paused by B-PERF-INSPECTION; owner full migration gates pending",
        mount_plan=dict(source=str(target),target=str(ROOT/REL),readonly=True),
        duplicate_CollisionBound_relays="Same base/target payload; staged once, not applied twice")
    (out/"overlay.json").write_text(json.dumps(manifest,indent=2,sort_keys=True)+"\n")
    print(json.dumps(manifest))
if __name__=="__main__":main()
