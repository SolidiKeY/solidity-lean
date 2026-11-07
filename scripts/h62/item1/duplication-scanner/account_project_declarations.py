#!/usr/bin/env python3
"""Guard fixture-only accounting and omission of unresolved project declarations.

Fresh admitted KeySort/AST/Scope producers only; no saved-receipt acceptance.
Retain exact legacy types/refusals and all source/range rows. No metadata-v2
promotion, generated identity inference, private/global completeness, ownership,
compiler adequacy, body equivalence or clearance of the held Lean workload.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import declaration_ledger as common
closure=common.closure
leaf=closure.leaf
binder=closure.binder
reader=leaf.source_binding.read_bound_json


def profile(target):
    if target=="keysort":return "Solidity/KeySort.lean",leaf.MODULE
    selected=closure.profile(target)
    return selected["expected"][-1][0],selected["module"]


def verify_capture(directory,live,digest,source_path,raw):
    """Recheck completed child observations, not fresh runtime recertification."""
    reader(directory/"receipt.json",digest)
    reader(directory/"metadata.json",live["metadata_sha256"])
    reader(directory/"source-bindings.json",live["bindings_sha256"])
    if (directory/"sources"/source_path).read_bytes()!=raw:raise ValueError("captured source changed during accounting")
    binder.verify_process_logs(live["steps"])
    fixture=reader(directory/"fixtures/receipt.json",live["fixture_receipt_sha256"])
    binder.verify_process_logs(fixture["steps"])


def run(output,target="keysort"):
    """Caller owns writer lease for the complete fresh producer and accounting."""
    source_path,module=profile(target)
    if not output.is_absolute():raise ValueError("output must be absolute")
    output.mkdir(mode=0o700,exist_ok=False)
    receipt={"schema":1,"kind":"fresh-project-declaration-ledger","status":"failed","target":target,"driver_sha256":binder.sha(Path(__file__)),"core_sha256":binder.sha(Path(common.__file__))}
    try:
        directory=output/"capture"
        live=leaf.run(directory) if target=="keysort" else closure.run(directory,target)
        if live["status"]!="pass" or live["keysort_gate"]!="pass":raise ValueError("project producer did not pass")
        digest=hashlib.sha256((json.dumps(live,indent=2)+"\n").encode()).hexdigest()
        reader(directory/"receipt.json",digest)
        legacy=reader(directory/"metadata.json",live["metadata_sha256"])
        bindings=reader(directory/"source-bindings.json",live["bindings_sha256"])
        if target=="keysort":source_sha=live["source_sha256"]
        else:
            sources=[r for r in live["fresh_project_closure"] if r["source"]==source_path]
            if len(sources)!=1:raise ValueError("target source count drift")
            source_sha=sources[0]["source_sha256"]
        raw=(directory/"sources"/source_path).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=source_sha or bindings["source_sha256"]!=source_sha:raise ValueError("captured source identity drift")
        lexical=binder.scanner.scan(binder.ROOT/source_path,binder.ROOT,raw)
        result=common.account(raw.decode(),lexical,legacy,bindings,source_path,module)
        verify_capture(directory,live,digest,source_path,raw)
        (output/"ledger.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
        receipt.update(status="pass",keysort_gate="pass",capture_receipt_sha256=digest,ledger_sha256=binder.sha(output/"ledger.json"),summary={k:result[k] for k in ("lexical_total","kernel_total","legacy_links","source_evidence_counts","legacy_type_statuses")},boundary=result["boundary"])
    except Exception as exc:receipt["error"]=str(exc);raise
    finally:(output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--output",type=Path,required=True);p.add_argument("--target",choices=("keysort","ast","scope"),default="keysort");args=p.parse_args()
    try:
        with binder.writer_lease():result=run(args.output,args.target)
    except (OSError,ValueError,RecursionError,subprocess.SubprocessError) as exc:p.exit(1,"PROJECT_ACCOUNTING_REJECT: "+str(exc)+"\n")
    print("PROJECT_DECLARATION_ACCOUNTING_PASS "+json.dumps(result["summary"]))


if __name__=="__main__":main()
