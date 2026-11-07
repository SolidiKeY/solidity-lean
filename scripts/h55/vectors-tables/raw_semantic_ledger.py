#!/usr/bin/env python3
"""Record a source-pinned human classification of the master Raw delta.

The ledger records statements and source hashes; it does not prove them or
establish semantic coverage of all other Raw modules.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import raw_master_reconcile as master
import raw_census as base

LOGIC = {
"formula_iff":"word formula and actual raw modal interpretation; both modalities",
"rule_premise_sound":"existing Rule premise and its side conditions remain required",
"diamond_implies_box":"completed diamond witness and deterministic completed outcomes",
"box_false_iff_none":"noncompletion at every fuel; one timeout is insufficient",
"diamond_iff_termination_and_box":"actual termination witness together with box postcondition",
"holds_completed":"requires an actual completed run; both modalities observe the whole outcome",
"holds_and":"both modalities; diamond reverse uses deterministic completed outcomes",
"holds_or":"both modalities; noncompletion gives vacuous box and absent diamond",
"box_not_iff_not_diamond":"box negation excludes a diamond witness",
"diamond_not_iff_not_box":"classical duality over actual completions",
"holds_mono":"whole-outcome implication; both modalities",
"skip_run":"skip returns a fully captured snapshot at fuel one",
"holds_skip":"postcondition observes captured snapshot; both modalities",
"holds_snapshot":"pre-capture of the same view; arbitrary whole-outcome postcondition",
"holds_agrees":"requires equal clean backup, world, and authoritative view",
"box_captured":"every completed outcome has full snapshot metadata; no completion asserted",
"box_not_sparse":"excludes a sparse alleged target, not all completion",
}
FRAME = {
"run_snapshot":"pre-capture of current view preserves exact run, including timeouts",
"run_agrees":"requires equal clean backup, world, and authoritative view",
"run_captured":"requires actual completed result; resulting state is fully captured",
"run_not_sparse":"missing raw cell excludes that alleged result, not completion generally",
}
HEADING = re.compile(r"^(?:def|theorem) ([A-Za-z_][A-Za-z0-9_\x27.]*)\b",re.M)

def declarations(text):
    hits=list(HEADING.finditer(text)); out={}
    for i,hit in enumerate(hits):
        name=hit.group(1)
        if name in out: raise ValueError("duplicate declaration")
        end=hits[i+1].start() if i+1<len(hits) else len(text)
        body=text[hit.start():end]
        marker=body.find(":= by")
        if marker<0: marker=body.find(":=")
        if marker<0: raise ValueError("unrecognized declaration schema")
        out[name]={"line":text.count("\n",0,hit.start())+1,"statement":body[:marker].strip(),"block_sha256":hashlib.sha256(body.encode()).hexdigest()}
    return out

def validate_inventory(logic, current, previous):
    if set(logic)!={"holds","formula",*LOGIC}: raise ValueError("logic declaration inventory differs")
    if set(current)-set(previous)!=set(FRAME) or set(previous)-set(current): raise ValueError("frame declaration delta differs")

def ledger(snapshot):
    meta,paths=master.snapshot(snapshot)
    path="Solidity/Yul/RawFrameLogic.lean"; frame="Solidity/Yul/RawFrame.lean"
    if path not in paths or frame not in paths: raise ValueError("required master inputs missing")
    logic=declarations((snapshot/path).read_text()); current=declarations((snapshot/frame).read_text())
    previous=declarations((base.ROOT/frame).read_text())
    validate_inventory(logic, current, previous)
    def rows(found, labels): return [{"name":name,"classification":label,**found[name]} for name,label in labels.items()]
    return {"base":base.BASE,"master":meta["commit"],"source_hashes":{p:meta["files"][p] for p in (path,frame)},"modal_definitions":[{"name":n,**logic[n]} for n in ("holds","formula")],"logic_theorems":rows(logic,LOGIC),"new_frame_theorems":rows(current,FRAME)}

def main():
    p=argparse.ArgumentParser(); p.add_argument("snapshot",type=Path); p.add_argument("output",type=Path); a=p.parse_args()
    out=a.output.resolve()
    if out.exists() or out.is_relative_to(base.ROOT): raise ValueError("new external output required")
    data=ledger(a.snapshot)
    out.write_text(json.dumps(data,ensure_ascii=False,indent=2)+"\n")
    print(f"PASS: {len(data['modal_definitions'])} modal definitions, {len(data['logic_theorems'])} logic and {len(data['new_frame_theorems'])} new frame theorems recorded")

if __name__ == "__main__": main()
