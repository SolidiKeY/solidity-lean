#!/usr/bin/env python3
"""Guard dropped imported constants and unresolved source rows in coverage reports.

A fresh versioned observation is required. Evidence categories describe recorded
ranges only: no generated/anonymous identity guesses, signature promotion, live
ownership, joint feasibility, body equivalence or runtime acceptance.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

import observe_metadata_types as observer
import declaration_ledger as common
closure=observer.closure
binder=observer.binder
SOURCE="Solidity/Scope.lean"


keyed=common.keyed


def account(source,lexical,legacy,bindings,observation):
    """Preserve the separate metadata observation and the original ledger format."""
    observer.validate(observation,legacy)
    result=common.account(source,lexical,legacy,bindings,SOURCE,closure.profile("scope")["module"])
    versions=keyed(observation["census"]["rows"])
    for row in result["constants"]:
        row["metadata_v2"]=versions[closure.leaf.kernel.name_key(row["legacy"]["declaration"])]["metadata_v2"]
    result["kind"]="lossless-observed-declaration-ledger"
    result["metadata_v2_type_statuses"]=dict(Counter(r["metadata_v2"]["status"] for r in result["constants"]))
    return result


def run(output):
    """Caller owns writer lease through fresh observation and final seals."""
    if not output.is_absolute():raise ValueError("output must be absolute")
    output.mkdir(mode=0o700,exist_ok=False)
    receipt={"schema":1,"status":"failed","kind":"fresh-observed-declaration-ledger","steps":[],"driver_sha256":binder.sha(Path(__file__)),"core_sha256":binder.sha(Path(common.__file__))}
    try:
        live=observer.run(output/"observed")
        live_hash=hashlib.sha256((json.dumps(live,indent=2)+"\n").encode()).hexdigest()
        reader=closure.leaf.source_binding.read_bound_json
        reader(output/"observed/receipt.json",live_hash)
        observation=reader(output/"observed/observation.json",live["observation_sha256"])
        directory=output/"observed/scope";scope=reader(directory/"receipt.json",live["scope_receipt_sha256"])
        legacy=reader(directory/"metadata.json",scope["metadata_sha256"])
        bindings=reader(directory/"source-bindings.json",scope["bindings_sha256"])
        target=[r for r in scope["fresh_project_closure"] if r["source"]==SOURCE]
        if len(target)!=1 or target[0]["source_sha256"]!=bindings["source_sha256"]:raise ValueError("Scope source identity drift")
        raw=(directory/"sources"/SOURCE).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=target[0]["source_sha256"]:raise ValueError("captured source bytes drift")
        lexical=binder.scanner.scan(binder.ROOT/SOURCE,binder.ROOT,raw)
        result=account(raw.decode(),lexical,legacy,bindings,observation)
        observer.verify_scope_artifacts(directory,scope,live["scope_receipt_sha256"])
        reader(output/"observed/receipt.json",live_hash);reader(output/"observed/observation.json",live["observation_sha256"])
        if (directory/"sources"/SOURCE).read_bytes()!=raw:raise ValueError("source changed during accounting")
        binder.verify_process_logs(live["steps"]);binder.verify_process_logs(scope["steps"])
        fixture=reader(directory/"fixtures/receipt.json",scope["fixture_receipt_sha256"]);binder.verify_process_logs(fixture["steps"])
        (output/"ledger.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
        receipt.update(status="pass",observation_receipt_sha256=live_hash,ledger_sha256=binder.sha(output/"ledger.json"),summary={k:result[k] for k in ["lexical_total","kernel_total","legacy_links","source_evidence_counts","legacy_type_statuses","metadata_v2_type_statuses"]},boundary=result["boundary"])
    except Exception as exc:receipt["error"]=str(exc);raise
    finally:(output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--output",type=Path,required=True);args=p.parse_args()
    try:
        with binder.writer_lease():result=run(args.output)
    except (OSError,ValueError,RecursionError,subprocess.SubprocessError) as exc:p.exit(1,"DECLARATION_ACCOUNTING_REJECT: "+str(exc)+"\n")
    print("OBSERVED_DECLARATION_ACCOUNTING_PASS "+json.dumps(result["summary"]))


if __name__=="__main__":main()
