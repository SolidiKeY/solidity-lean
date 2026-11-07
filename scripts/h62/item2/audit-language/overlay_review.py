#!/usr/bin/env python3
"""Authenticate partial owner patches and compare frozen source headers.
Never applies a patch to a file or compiles an overlay. Transport/fidelity
checks imply neither owner agreement, edit permission nor Lean validation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from census import BASE,mask,scan
from classify import declaration_index

TRUSTED={
 "collision-bound":{"path":"Solidity/Hash/CollisionBound.lean","sha256":"3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff","owner":"solidity-h62-6-20261106/migrate-hash","ticket":"a3f49ee0ec1829e63022c90194048d5a1ffe0d22","source":"2a18afcdba00a85645b0b3079704f78ffcd78860"},
 "fixedpoint":{"path":"Solidity/Language/FixedPoint.lean","sha256":"a3cbeea6c8a243df761166dd558825898f2bbda8c8fa7d8a74850cd27cb8ad82","owner":"solidity-h62-6-20261106/migrate-language","ticket":"479f6e0079409a1867483dbffe5051932b8fa754","source":"d8e1d9721455d3671882f19aa7155fbbd2d91415"}}

def blob(data): return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()

def reconstruct(patch,original,expected_path):
    """Strict single-file unified patch in memory; no offsets/fuzz/repair."""
    lines=patch.decode().splitlines(keepends=True)
    if len(lines)<5: raise ValueError("truncated patch")
    expected=f"diff --git a/{expected_path} b/{expected_path}\n"
    if lines[0]!=expected or sum(x.startswith("diff --git ") for x in lines)!=1:
        raise ValueError("unexpected path or multiple files")
    match=re.fullmatch(r"index ([0-9a-f]+)\.\.([0-9a-f]+) 100644\n",lines[1])
    if not match or not blob(original).startswith(match[1]): raise ValueError("original blob mismatch")
    if lines[2]!=f"--- a/{expected_path}\n" or lines[3]!=f"+++ b/{expected_path}\n": raise ValueError("unexpected file headers")
    source=original.decode().splitlines(keepends=True);output=[];cursor=0;i=4;hunks=0
    while i<len(lines):
        h=re.fullmatch(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@[^\n]*\n",lines[i])
        if not h: raise ValueError("malformed hunk header")
        start,count,new_start,new_count=int(h[1]),int(h[2] or 1),int(h[3]),int(h[4] or 1)
        if start<1 or start-1<cursor: raise ValueError("overlapping/out-of-order hunk")
        output.extend(source[cursor:start-1])
        if new_start!=len(output)+1: raise ValueError("new hunk position mismatch")
        old=[];new=[];i+=1
        while i<len(lines) and not lines[i].startswith("@@ "):
            line=lines[i]
            if not line or line[0] not in " +-": raise ValueError("unsupported/malformed hunk content")
            if line[0] in " -":old.append(line[1:])
            if line[0] in " +":new.append(line[1:])
            i+=1
        if len(old)!=count or len(new)!=new_count: raise ValueError("hunk line-count mismatch")
        if source[start-1:start-1+count]!=old: raise ValueError("hunk context differs from frozen blob")
        output.extend(new);cursor=start-1+count;hunks+=1
    output.extend(source[cursor:]);result="".join(output).encode()
    if not blob(result).startswith(match[2]): raise ValueError("postimage blob mismatch")
    return result,hunks,match[1],match[2]

def fidelity(path,original,updated):
    before=scan(path,original,{"source-audit"});after=scan(path,updated,{"source-audit"})
    keys=lambda rows:[(r["name_candidate"],r["source_signature"],r["section_variables"]) for r in rows]
    if keys(before)!=keys(after): raise ValueError("frozen theorem header/context changed")
    old_symbols,_=declaration_index({path:original.decode()});new_symbols,_=declaration_index({path:updated.decode()})
    headers=lambda symbols:[(r["name"],r["kind"],r["declared_result"],r["parameters"]) for r in symbols.values()]
    if headers(old_symbols)!=headers(new_symbols): raise ValueError("source declaration header changed")
    old,new=mask(original.decode()),mask(updated.decode())
    for forbidden in (r"\bsorry\b",r"\baxiom\b",r"\bnative_decide\b"):
        if len(re.findall(forbidden,new))>len(re.findall(forbidden,old)): raise ValueError("new forbidden source trust escape")
    options=lambda text:re.findall(r"(?m)^\s*set_option[^\n]*",text)
    if options(old)!=options(new): raise ValueError("source options/budgets changed")
    return {"theorem_headers":len(before),"declaration_headers":len(old_symbols),
            "statement_fidelity":"source headers and captured section variables identical; elaborated fidelity pending"}

def review(row):
    trusted=TRUSTED.get(row.get("label"))
    if trusted is None:raise ValueError("unregistered owner receipt")
    for supplied,key in (("owner","owner"),("expected_sha256","sha256"),("reported_ticket_head","ticket"),("reported_source_head","source")):
        if row.get(supplied)!=trusted[key]:raise ValueError("receipt metadata differs from coordinator identity")
    patch=Path(row["path"]).read_bytes();actual=hashlib.sha256(patch).hexdigest()
    if actual!=trusted["sha256"]:raise ValueError("patch SHA256 mismatch")
    original=subprocess.check_output(["git","show",f"{BASE}:{trusted['path']}"])
    updated,hunks,old_id,new_id=reconstruct(patch,original,trusted["path"])
    checked=fidelity(trusted["path"],original,updated)
    if Path(trusted["path"]).read_bytes()!=original:raise ValueError("owned original differs from frozen base")
    return dict(checked,label=row["label"],owner=row["owner"],path=trusted["path"],
                patch_sha256=actual,original_blob=blob(original),postimage_blob=blob(updated),hunks=hunks,
                transport="authenticated-by-coordinator-advertised-SHA256",applicability="strict-in-memory-pass",
                ownership_agreement="not-established-by-relay",original_edit_permission="not-granted",
                Lean_validation="pending; partial producer overlays do not establish a passing gate",
                patch_applied=False,reported_ticket_head=row["reported_ticket_head"],reported_source_head=row["reported_source_head"])

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--registry",type=Path,required=True);p.add_argument("--output",type=Path,required=True);args=p.parse_args()
    if args.output.resolve().is_relative_to(Path(__file__).resolve().parents[4]):raise ValueError("bulk evidence must be outside repository")
    rows=json.loads(args.registry.read_text())
    if {r.get("label") for r in rows}!=set(TRUSTED) or len(rows)!=len(TRUSTED):raise ValueError("missing or duplicate overlay receipt")
    reports=[review(row) for row in rows]
    args.output.mkdir(parents=True,exist_ok=True)
    payload=(json.dumps({"base":BASE,"status":"source-receipt-review-only","overlays":reports,"new_witnesses":0,"full_migration_gates":"pending"},indent=2)+"\n").encode()
    (args.output/"overlay-review.json").write_bytes(payload)
    (args.output/"overlay-review.sha256").write_text(hashlib.sha256(payload).hexdigest()+"  overlay-review.json\n")
    print(json.dumps({"status":"PASS-source-receipt-review-only","overlays":len(reports),"theorem_headers":sum(r["theorem_headers"] for r in reports),"applied":False,"Lean_validation":"pending"}))

if __name__=="__main__":main()
