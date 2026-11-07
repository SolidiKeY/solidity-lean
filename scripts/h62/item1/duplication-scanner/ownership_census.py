#!/usr/bin/env python3
"""Guard stale-owner promotion and cross-chain allocation leakage.

Authenticated allocation and Git provenance are separate evidence. A matching
new-file pattern, an absent owner, or a candidate-path superset never grants
ownership of an existing file and never establishes an unowned opportunity.
"""
import argparse
from collections import Counter
import fnmatch
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import stat
import subprocess

MANIFEST_SHA256 = "39fb14a45e1e34042b75922e8d60da77f4b6a3555bcae718a8f95e4c37d3055b"
SELF = "solidity-h62-2-20261106/audit-readonly-calls"
TRUSTED_CLEANUP_HEAD = "fc59bfc04c76e25e259b5b5b43e0349007b6c870"  # H70 requester head authenticated by coordinator
SELF_BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
SELF_PREFIXES = ("scripts/h62/item2/audit-readonly-calls/", "tests/h62/item2/audit-readonly-calls/")
SELF_DOC = "docs/feature-work/h62-2-audit-readonly-calls.md"


def load_authority(receipt):
    raw=(receipt/"manifest.json").read_bytes()
    if hashlib.sha256(raw).hexdigest()!=MANIFEST_SHA256:
        raise ValueError("unauthenticated H82b manifest")
    manifest=json.loads(raw)
    def load(relative):
        path=receipt/relative
        if path.resolve().parent != receipt.resolve() and not path.resolve().is_relative_to(receipt.resolve()):
            raise ValueError("receipt path escapes root")
        data=path.read_bytes()
        if hashlib.sha256(data).hexdigest()!=manifest["files"][relative]:
            raise ValueError("authenticated receipt file hash mismatch")
        return data
    members={}
    scope=None
    for lane,item in manifest["members"].items():
        if item["chain"]!="cleanup":continue
        if not item["verified_final_stop_head_pause"]:
            raise ValueError("unverified final member")
        assignment=json.loads(load(item["assignment"]))
        current_scope=json.loads(load(item["scope"]))
        if scope is not None and scope!=current_scope:raise ValueError("inconsistent chain scope")
        scope=current_scope
        report=load(item["final_report"]).decode()
        blocks=re.findall(r"(?ms)^CLOUDVM-RESULT\n(.*?)\nEND-CLOUDVM-RESULT",report)
        if len(blocks)!=1:raise ValueError("ambiguous member result")
        result=json.loads(blocks[0])
        if assignment["lane"]!=lane or result["head"]!=item["head"] or load(item["head_file"]).decode().strip()!=item["head"]:
            raise ValueError("member identity mismatch")
        if not re.fullmatch(r"[0-9a-f]{40}",result["base"]):raise ValueError("member base")
        members[lane]={"head":item["head"],"base":result["base"]}
    if len(members)!=5 or scope["write_namespace"]!="live":raise ValueError("wrong cleanup allocation")
    foreign=[]
    for chain,allocation in manifest["chains"].items():
        if chain=="cleanup":continue
        name=allocation["assignment_directory"]+"/scope.json"
        other=json.loads(load(name))
        if other["write_namespace"]!="live":continue
        for pattern in other["exclusive_files"]:
            foreign.append({"chain":chain,"pattern":pattern,"scope_file":name,
                            "scope_sha256":manifest["files"][name]})
    scope["_foreign_live_allocations"]=foreign
    return scope,members


def in_new_scope(path,scope):
    return any(fnmatch.fnmatchcase(path,p) for p in scope["new_file_scope"])


def classify(path,clean,scope,claimants,provenance_bound=True,tracked=True,foreign=False):
    if Path(path).is_absolute() or ".." in Path(path).parts:raise ValueError("unsafe census path")
    if not tracked:return {"allocation_status":"untracked-or-ignored-owner-review","owner":"unknown"}
    if not clean:return {"allocation_status":"working-tree-drift-owner-review","owner":"unknown"}
    if foreign:
        if path in scope["exclusive_files"] or (in_new_scope(path,scope) and claimants and provenance_bound):
            return {"allocation_status":"conflicting-authenticated-allocations-owner-review","owner":"unknown"}
        return {"allocation_status":"foreign-chain-allocation-read-only","owner":"unknown"}
    if len(claimants)>1:return {"allocation_status":"ambiguous-member-provenance","owner":"unknown"}
    if path in scope["exclusive_files"]:
        return {"allocation_status":"authenticated-cleanup-exclusive","owner":SELF}
    if in_new_scope(path,scope) and len(claimants)==1:
        if not provenance_bound:return {"allocation_status":"post-member-blob-owner-review","owner":"unknown"}
        return {"allocation_status":"cleanup-allocation-and-member-git-provenance","owner":SELF}
    if in_new_scope(path,scope):
        return {"allocation_status":"new-file-pattern-only-existing-owner-review","owner":"unknown"}
    return {"allocation_status":"outside-cleanup-allocation-read-only","owner":"unknown"}


def git(root,*args):return subprocess.check_output(["git",*args],cwd=root)


def additions(root,base,head):
    return set(filter(None,git(root,"diff","--diff-filter=A","--name-only","-z",base,head).decode().split("\0")))


def tree_blobs(root,head):
    return {name.decode():meta.decode().split()[2]
            for entry in git(root,"ls-tree","-rz",head).split(b"\0") if entry
            for meta,name in [entry.split(b"\t",1)]}


def blob_provenance(path,blob,claims,member_blobs,checkpoint_blobs):
    return bool(claims) and (checkpoint_blobs.get(path)==blob or
           any(member_blobs.get(lane,{}).get(path)==blob for lane in claims))


def scanner_inputs(root):
    """Guard nested-repository omission by using the scanner's own selection rules."""
    path=Path(__file__).with_name("scan.py")
    spec=importlib.util.spec_from_file_location("ownership_selector",path)
    selector=importlib.util.module_from_spec(spec);spec.loader.exec_module(selector)
    errors=[];paths=set()
    for pattern in ("Solidity/**/*.lean","Bridge/**/*.lean","tests/**/*.lean","*.lean"):
        for file in selector.selected_paths(root,pattern,errors):
            if file.suffix==".lean":paths.add(file.relative_to(root).as_posix())
    return paths,errors


def census(root,receipt):
    scope,members=load_authority(receipt)
    head=git(root,"rev-parse","HEAD").decode().strip()
    if subprocess.run(["git","merge-base","--is-ancestor",TRUSTED_CLEANUP_HEAD,head],cwd=root).returncode:
        raise ValueError("checkout does not descend from authenticated cleanup checkpoint")
    claims={};missing=[];member_blobs={}
    checkpoint_blobs=tree_blobs(root,TRUSTED_CLEANUP_HEAD)
    for lane,item in members.items():
        if subprocess.run(["git","cat-file","-e",item["head"]+"^{commit}"],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode:
            missing.append(lane);continue
        if subprocess.run(["git","merge-base","--is-ancestor",item["head"],head],cwd=root).returncode:
            missing.append(lane);continue
        member_blobs[lane]=tree_blobs(root,item["head"])
        for path in additions(root,item["base"],item["head"]):
            if in_new_scope(path,scope):claims.setdefault(path,[]).append(lane)
    if git(root,"branch","--show-current").decode().strip()!="codex/"+SELF:
        raise ValueError("self provenance requires assigned branch")
    for path in additions(root,SELF_BASE,head):
        if path.startswith(SELF_PREFIXES) or path==SELF_DOC:
            claims.setdefault(path,[]).append(SELF)
    algorithm=git(root,"rev-parse","--show-object-format").decode().strip()
    entries={}
    for entry in git(root,"ls-tree","-rz",head).split(b"\0"):
        if entry:
            meta,name=entry.split(b"\t",1);mode,kind,blob=meta.decode().split()
            entries[name.decode()]=(mode,blob,True)
    for ignored in (False,True):
        args=["ls-files","--others","--exclude-standard","-z"]+(["--ignored"] if ignored else [])
        for path in git(root,*args).decode().split("\0"):
            if not path:continue
            lean_input=path.endswith(".lean") and (path.startswith(("Solidity/","Bridge/","tests/")) or "/" not in path)
            if lean_input or in_new_scope(path,scope) or path in scope["exclusive_files"]:
                entries.setdefault(path,(None,None,False))
    selected,selection_errors=scanner_inputs(root)
    for path in selected:entries.setdefault(path,(None,None,False))
    foreign_exact={};foreign_patterns=[]
    for hint in scope["_foreign_live_allocations"]:
        pattern=hint["pattern"]
        if any(c in pattern for c in "*?["):foreign_patterns.append(hint)
        else:foreign_exact.setdefault(pattern,[]).append(hint)
    rows=[]
    for path,(mode,blob,tracked) in sorted(entries.items()):
        if not (path.endswith(".lean") or in_new_scope(path,scope) or path in scope["exclusive_files"]):continue
        row={"path":path,"git_mode":mode,"head_blob":blob,"tracked_at_head":tracked,"member_provenance":sorted(claims.get(path,[]))}
        clean=False
        try:
            file=root/path;before=file.lstat()
            if not stat.S_ISREG(before.st_mode):raise ValueError("nonregular source requires ownership review")
            data=file.read_bytes();after=file.lstat()
            fingerprint=lambda s:(s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
            if fingerprint(before)!=fingerprint(after):raise ValueError("source changed during census")
            actual=hashlib.new(algorithm,b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
            row.update(source_sha256=hashlib.sha256(data).hexdigest(),current_blob=actual)
            clean=actual==blob
        except (OSError,ValueError) as exc:row["source_error"]=str(exc)
        bound=blob_provenance(path,blob,row["member_provenance"],member_blobs,checkpoint_blobs)
        row["member_or_authenticated_checkpoint_blob_matches"]=bound
        hints=foreign_exact.get(path,[])+[r for r in foreign_patterns if fnmatch.fnmatchcase(path,r["pattern"])]
        row["foreign_allocation_hints"]=hints
        row.update(classify(path,clean,scope,row["member_provenance"],bound,tracked,bool(hints)));rows.append(row)
    expected=set(scope["exclusive_files"])
    return {"schema":1,"head":head,"receipt_manifest_sha256":MANIFEST_SHA256,"trusted_cleanup_checkpoint":TRUSTED_CLEANUP_HEAD,"rows":rows,
            "counts":dict(Counter(r["allocation_status"] for r in rows)),
            "scanner_input_count":len(selected),"selection_errors":selection_errors,
            "foreign_hint_boundary":"Authenticated H82b live-chain allocation exclusions only, not current producer routing, scope transfer or an unowned grant; migration-only allocations are ignored.",
            "selector_sha256":hashlib.sha256(Path(__file__).with_name("scan.py").read_bytes()).hexdigest(),
            "missing_member_git_provenance":missing,
            "absent_exclusive_files":sorted(expected-{r["path"] for r in rows}),
            "checkout_status":git(root,"status","--porcelain").decode(),
            "boundary":"Authenticated cleanup allocation and exact Git provenance; tracked Lean/cleanup files plus untracked/ignored scanner-area Lean inputs and cleanup files are accounted. Other owners stay unknown/read-only; untracked/ignored data never gains an ownership grant. No unowned opportunities or declaration/signature equivalence established."}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root",type=Path,required=True);p.add_argument("--receipt",type=Path,required=True);p.add_argument("--output",type=Path,required=True)
    a=p.parse_args();result=census(a.root.resolve(),a.receipt.resolve());a.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"rows":len(result["rows"]),"counts":result["counts"],"missing_member_git_provenance":result["missing_member_git_provenance"],"unowned_opportunities_established":0}))
    return 1 if result["selection_errors"] or any("source_error" in r or r["allocation_status"]=="working-tree-drift-owner-review" for r in result["rows"]) else 0


if __name__=="__main__":raise SystemExit(main())
