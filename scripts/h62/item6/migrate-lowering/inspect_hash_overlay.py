#!/usr/bin/env python3
"""Inspect an owner-provided partial patch without changing any production source."""
import hashlib,json,re,subprocess
from pathlib import Path
EXPECTED="3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff"
TARGET="Solidity/Hash/CollisionBound.lean"

def blob(data):return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()

def patched_bytes(original,patch):
    src=original.decode().splitlines(keepends=True);lines=patch.decode().splitlines(keepends=True);out=[];cursor=0;i=0;hunks=0
    while i<len(lines):
        m=re.match(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@",lines[i])
        if not m:i+=1;continue
        start=int(m[1])-1;old=int(m[2] or 1);new=int(m[4] or 1)
        if start<cursor:raise ValueError("overlapping/out-of-order hunks")
        out.extend(src[cursor:start]);cursor=start;consumed=produced=0;i+=1
        while i<len(lines) and not lines[i].startswith("@@"):
            line=lines[i];tag=line[:1];body=line[1:]
            if tag in (" ","-"):
                if cursor>=len(src) or src[cursor]!=body:raise ValueError("patch context mismatch")
                cursor+=1;consumed+=1
            if tag in (" ","+"):out.append(body);produced+=1
            if tag not in (" ","-","+"):raise ValueError("unsupported patch line")
            i+=1
        if (consumed,produced)!=(old,new):raise ValueError("hunk counts mismatch")
        hunks+=1
    if not hunks:raise ValueError("no patch hunks")
    out.extend(src[cursor:]);return "".join(out).encode(),hunks

if __name__=="__main__":
    root=Path.cwd();input_path=root/"tests/h62/item6/migrate-lowering/owner-inputs/collision-bound-overlay.json"
    encoded=json.loads(input_path.read_text());patch=("\n".join(encoded["patch_lines"])+"\n").encode()
    if encoded["sha256"]!=EXPECTED:raise SystemExit("encoded receipt digest mismatch")
    if hashlib.sha256(patch).hexdigest()!=EXPECTED:raise SystemExit("owner patch SHA256 mismatch")
    p=Path("/workspace/migrate-lowering-artifacts/evidence/owner-inputs/collision-bound-overlay.patch")
    p.parent.mkdir(exist_ok=True)
    if p.exists() and p.read_bytes()!=patch:raise SystemExit("refusing to replace a different receipt")
    p.write_bytes(patch)
    original=(root/TARGET).read_bytes()
    if not blob(original).startswith("b54c93a5b"):raise SystemExit("owner patch base differs; review required")
    targets=re.findall(r"^diff --git a/(.+) b/(.+)$",patch.decode(),re.M)
    if targets!=[(TARGET,TARGET)]:raise SystemExit("unexpected patch target")
    checked=subprocess.run(["git","apply","--check",str(p)],capture_output=True,text=True)
    if checked.returncode:raise SystemExit(checked.stderr)
    after,hunks=patched_bytes(original,patch)
    if not blob(after).startswith("092971eda"):raise SystemExit("owner target blob mismatch")
    assert original==(root/TARGET).read_bytes(),"production source changed during inspection"
    result={"owner":"solidity-h62-6-20261106/migrate-hash","owner_head":"a3f49ee0ec1829e63022c90194048d5a1ffe0d22","owner_reported_source":"2a18afcd","owner_commits_independently_verified":False,"encoded_input_sha256":hashlib.sha256(input_path.read_bytes()).hexdigest(),"raw_patch":str(p),"patch_sha256":EXPECTED,"inline_matches_advertised_receipt":True,"base_blob":blob(original),"candidate_blob":blob(after),"candidate_source_sha256":hashlib.sha256(after).hexdigest(),"hunks":hunks,"apply_check_exit":checked.returncode,"production_source_changed":False,"host_receipt_path_accessible":False,"host_relay_journal_inspected":False,"status":"partial-owner-input-received-not-validated","affected_Lean_gates":"pending per owner; not run here while serial supervisor active","API_axiom_performance_acceptance":False,"boundary":"SHA/base/applicability/candidate-blob checks are not Lean proof, API equality, axiom acceptance, owner agreement or full affected validation. Fixed supplied patch format only; owner commit IDs are reported provenance. No patch applied to production or test Lean source."}
    out=Path("/workspace/migrate-lowering-artifacts/evidence/hash-collision-overlay-inspection.json");out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True))
