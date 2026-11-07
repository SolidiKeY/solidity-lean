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
closure=observer.closure
binder=observer.binder
SOURCE="Solidity/Scope.lean"


def keyed(rows):
    result={}
    for row in rows:
        key=closure.leaf.kernel.name_key(row["declaration"])
        if key in result:raise ValueError("duplicate declaration identity")
        result[key]=row
    return result


def account(source,lexical,legacy,bindings,observation):
    """Structural accounting only; saved packets do not authenticate execution."""
    observer.validate(observation,legacy)
    expected=closure.leaf.source_binding.join_locations(source,lexical,legacy["census"],legacy["locations"],closure.profile("scope")["module"])
    if expected!=bindings:raise ValueError("source binding correspondence drift")
    known=keyed(legacy["census"]["rows"]);locations=keyed(legacy["locations"]["rows"]);versions=keyed(observation["census"]["rows"])
    linked={};sources=[]
    for index,(row,bound) in enumerate(zip(lexical,bindings["rows"])):
        if row["path"]!=SOURCE:raise ValueError("foreign lexical source")
        sources.append({"index":index,"lexical":row,"legacy_binding":bound,"ownership":"unverified","body_equivalence":"unproved"})
        if bound["status"]=="direct-source-signature-link":
            key=closure.leaf.kernel.name_key(bound["declaration"])
            if key in linked:raise ValueError("multiple source rows claim one declaration")
            linked[key]=index
    constants=[]
    for key,row in known.items():
        selection=locations[key]["selection"];fragment=None
        if key in linked:
            state="existing-direct-source-link"
        elif selection is None:
            state="no-compiler-range"
        else:
            fragment=closure.leaf.source_binding.source_slice(source,selection)
            if key[-1]!=("str",fragment):state="range-name-differs"
            else:state="direct-range-without-legacy-link"
        constants.append({"legacy":row,"metadata_v2":versions[key]["metadata_v2"],"selection":selection,
                          "source_evidence":{"status":state,"lexical_index":linked.get(key),"selected_fragment":fragment},
                          "ownership":"unverified","unloaded_private_coverage":"unproved"})
    if len(constants)!=bindings["visible_kernel_total"] or len(sources)!=bindings["lexical_total"]:raise ValueError("accounting cardinality drift")
    return {"schema":1,"kind":"lossless-observed-declaration-ledger","source_path":SOURCE,"source_sha256":bindings["source_sha256"],
            "lexical_total":len(sources),"kernel_total":len(constants),"legacy_links":len(linked),"sources":sources,"constants":constants,
            "source_evidence_counts":dict(Counter(r["source_evidence"]["status"] for r in constants)),
            "lexical_binding_statuses":dict(Counter(r["legacy_binding"]["status"] for r in sources)),
            "legacy_type_statuses":dict(Counter(r["legacy"]["status"] for r in constants)),
            "metadata_v2_type_statuses":dict(Counter(r["metadata_v2"]["status"] for r in constants)),
            "boundary":"Every observed imported constant and selected lexical row counted once. Range categories are observations, not generated-identity inference, global/private completeness, signature promotion, ownership, feasibility or body equivalence. Original792 obligations and Lean timing STOP unchanged."}


def run(output):
    """Caller owns writer lease through fresh observation and final seals."""
    if not output.is_absolute():raise ValueError("output must be absolute")
    output.mkdir(mode=0o700,exist_ok=False)
    receipt={"schema":1,"status":"failed","kind":"fresh-observed-declaration-ledger","steps":[],"driver_sha256":binder.sha(Path(__file__))}
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
