#!/usr/bin/env python3
"""Reconcile frozen source, fresh kernel exports and exact joint proof receipts."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
sys.dont_write_bytecode=True
from owners import inventory
from receipts import HELPER, sha, validate_export, find_direct_compile, validate_dependency_edge
from bounded_lean import imports
from reconcile import reconcile_sources, verification_requests

BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence",required=True,type=Path)
    parser.add_argument("--require-complete",action="store_true")
    args=parser.parse_args()
    root,evidence=Path.cwd(),args.evidence.resolve()
    if evidence.is_relative_to(root):parser.error("H44: bulk evidence must be outside git")
    output=evidence/"acceptance.json"
    output.unlink(missing_ok=True)
    subprocess.run(["git","diff","--exit-code",BASE,"--","Solidity","vendor/LeanTeX","docs/module-map"],check=True,stdout=subprocess.DEVNULL)
    source=json.loads((evidence/"source-census.json").read_text())
    files=[row["path"] for row in source["sources"]]
    for row in source["sources"]:
        if sha(root/row["path"])!=row["sha256"]:raise RuntimeError("stale frozen source hash")
    ownership=inventory(files)
    records=[json.loads(line) for line in (evidence/"baseline/lean-commands.jsonl").read_text().splitlines()]
    compiled={r["file"]:r for r in records if r.get("kind","compile") in {"compile","compile-cache"}}
    exports={r["file"]:r for r in records if r.get("kind")=="kernel-census"}
    certified_cache={}
    def certified(file):
        if file in certified_cache:return certified_cache[file]
        r=compiled.get(file,{})
        artifact=r.get("artifact")
        if r.get("schema")!=2 or r.get("exit")!=0 or not artifact or r.get("source_sha256")!=sha(root/file) or r.get("artifact_sha256")!=sha(artifact):
            raise RuntimeError("no current source-bound compile: "+file)
        dependencies=r.get("dependency_artifact_hashes",{})
        if set(dependencies)!=set(imports(root,file)):raise RuntimeError("incomplete dependency receipt: "+file)
        direct=find_direct_compile(records,file,sha(root/file),sha(artifact),dependencies,r.get("lean_sha256"))
        if direct is None:raise RuntimeError("artifact lacks a hash-bound direct compile: "+file)
        for dep,digest in dependencies.items():
            validate_dependency_edge(r,certified(dep),digest)
        certified_cache[file]=r;return r
    kernel,scoped_kernel,exported,unrefreshed={},set(),[],[]
    for file,record in sorted(exports.items()):
        if record.get("schema")!=2:
            if file in files:unrefreshed.append(file)
            continue
        item=validate_export(record,root,certified(file),certified(record.get("helper_file",HELPER)))
        if file in files:exported.append(file)
        for theorem in item["theorems"]:
            key=(item["module"],theorem["name"])
            if key in kernel:raise RuntimeError("duplicate kernel statement in module")
            kernel[key]=dict(theorem,module=item["module"],file=file)
            if file in files:scoped_kernel.add(key)
    unrefreshed=sorted(set(files)-set(exported))
    witnesses={}
    for file in sorted((root/"tests/h62/item2/audit-calculus").glob("*Witnesses.lean")):
        relative=str(file.relative_to(root));receipt=certified(relative)
        if receipt.get("schema")!=2 or receipt.get("exit")!=0 or receipt.get("source_sha256")!=sha(file):
            raise RuntimeError("missing passing current-source proof receipt: "+relative)
        if sha(receipt["log"])!=receipt["log_sha256"] or sha(receipt["artifact"])!=receipt["artifact_sha256"]:
            raise RuntimeError("proof receipt log/artifact changed: "+relative)
        for dep,digest in receipt["dependency_artifact_hashes"].items():
            artifact=(evidence/"baseline/private-olean"/dep.removeprefix("vendor/LeanTeX/")).with_suffix(".olean")
            if sha(artifact)!=digest:raise RuntimeError("stale proof dependency: "+dep)
        log=Path(receipt["log"]).read_text()
        if re.search(r"(?m)^.*\.lean:\d+:\d+: (?:error|warning):",log):raise RuntimeError("proof diagnostics: "+relative)
        expected=verification_requests(file.read_text())
        verified=[json.loads(line.split("H62_JOINT_VERIFIED ",1)[1]) for line in log.splitlines() if "H62_JOINT_VERIFIED " in line]
        if len(expected)!=len(verified):raise RuntimeError("joint verification count mismatch")
        for (original,short,encoding),record in zip(expected,verified):
            if record["original"]!=original or record["witness"].split(".")[-1]!=short:raise RuntimeError("joint identity mismatch")
            key=(record.get("original_module"),original)
            if key in witnesses:raise RuntimeError("original statement counted twice")
            if set(record["axioms"])-{"propext","Classical.choice","Quot.sound"}:raise RuntimeError("unexpected witness axiom")
            if key not in kernel:raise RuntimeError("joint proof lacks a fresh module export: "+str(key))
            if encoding!=record.get("original_type_expression_format","repr-v1") or encoding!=kernel[key].get("type_expression_format","repr-v1"):
                raise RuntimeError("joint/kernel expression encoding differs")
            if record["original_type_expression"]!=kernel[key]["type_expression"]:
                raise RuntimeError("exact joint/kernel statement expression differs: "+str(key))
            witnesses[key]=dict(record,file=relative)
    identities=reconcile_sources(source["declarations"],kernel)
    accounted=[];matched_keys=set()
    for row in source["declarations"]:
        key=identities.get(row["id"])
        record=dict(row,ownership=ownership[row["file"]])
        record["owner"]="See separate writer contact and producer routing; exact semantic producer pending"
        if key is not None:
            statement=kernel[key]
            record["kernel_statement"]=statement
            record["signature_status"]="source identity uniquely matched to exact kernel type, independently of witness"
            record["hypotheses"]="exact dependent telescope exported; semantic role classification pending"
        if key in witnesses:
            record["joint_witness"]=witnesses[key];matched_keys.add(key)
            record["hypotheses"]=("all leading inputs jointly checked; fixture-level feasibility only"
                if kernel[key]["binders"] else
                "closed input telescope checked; semantic conditions inside the conclusion remain pending")
            record["semantic_conclusion_audit"]="pending; joint feasibility does not clear embedded preconditions or admission"
        accounted.append(record)
    supporting={key:value for key,value in witnesses.items() if key not in matched_keys}
    for key in supporting:
        if kernel[key]["file"] in files:raise RuntimeError("mapped joint receipt lacks source match")
    # Supporting transitive-interface witnesses never inflate mapped coverage.
    source_keys=set(identities.values())
    additional=[dict(row,status="pending generated/private/projection classification") for key,row in sorted(kernel.items()) if key in scoped_kernel and key not in source_keys]
    unresolved=[file for file in files if not ownership[file]["writer_contacts"]]
    counts={"source_candidates":len(accounted),"exact_kernel_matched_source_candidates":len(identities),
            "source_signatures_pending":len(accounted)-len(identities),"verified_source_joint_witnesses":len(matched_keys),"supporting_dependency_joint_witnesses":len(supporting),
            "source_candidates_uncovered":len(accounted)-len(matched_keys),"fresh_kernel_modules":len(exported),
            "kernel_theorems_in_fresh_modules":len(scoped_kernel),"additional_kernel_candidates_uncovered":len(additional),
            "writer_contacts_resolved_files":len(files)-len(unresolved),"writer_contacts_unresolved_files":len(unresolved)}
    counts["verified_source_input_bearing_witnesses"]=sum(bool(kernel[key]["binders"]) for key in matched_keys)
    counts["verified_source_closed_telescope_checks"]=sum(not kernel[key]["binders"] for key in matched_keys)
    counts["distinct_witness_theorems"]=len({row["witness"] for row in witnesses.values()})
    result={"base":BASE,"audit_status":"partial","source_candidates":accounted,"additional_kernel_theorems":additional,
            "supporting_dependency_witnesses":list(supporting.values()),"owner_inventory":ownership,"unresolved_writer_files":unresolved,"kernel_export_pending_files":unrefreshed,
            "counts":counts,"limitations":["full statement census and semantic premise classification unfinished",
            "all semantic producer owners require exact-file confirmation","full source compiler totality and gas/fork/world boundaries pending",
            "full affected validation and controlled performance gate pending"]}
    output=evidence/"acceptance.json";output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print(json.dumps({"status":"partial","output":str(output),"sha256":sha(output),**counts},sort_keys=True))
    if args.require_complete and (counts["source_candidates_uncovered"] or additional or unrefreshed or unresolved or result["limitations"]):raise SystemExit(1)


if __name__=="__main__":main()
