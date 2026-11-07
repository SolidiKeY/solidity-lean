#!/usr/bin/env python3
"""Guard metadata stripping and v2 observations promoted to legacy signatures.

Fresh Scope binding is a prerequisite, never an accepted saved receipt. This
additional observation retains legacy records exactly and uses a separate domain.
No scanner annotation, equivalence, witness, ownership or runtime acceptance.
"""
import argparse
from collections import Counter
import hashlib
import json
import re
from pathlib import Path
import subprocess

import bind_project_closure as closure
binder=closure.binder
PINS=binder.FIXTURES/"metadata-observation-pins.json"
HELPER=binder.FIXTURES/"MetadataFingerprintV2.lean"
PROBE=binder.FIXTURES/"ScopeMetadataObservation.lean"
PREFIX="H62_METADATA_OBSERVATION "


def admitted(pins):
    if pins.get("schema")!=1 or binder.regular(HELPER)["sha256"]!=pins["helper_sha256"] or binder.regular(PROBE)["sha256"]!=pins["probe_sha256"]:
        raise ValueError("metadata observation source drift")
    for path,expected in [(HELPER,["SignatureFingerprint"]),(PROBE,["SignatureEnvironment","MetadataFingerprintV2","Solidity.Scope"])]:
        source=binder.scanner.hide_strings(binder.scanner.mask(path.read_text()))
        if [x.strip() for x in re.findall(r"(?m)^\s*(?:(?:public|meta)\s+)*import\s+([^\n]+)",source)]!=expected:
            raise ValueError("unadmitted observation imports")
    if binder.sha(closure.profile("scope")["pins"])!=pins["scope_contract_sha256"]:raise ValueError("Scope contract drift")


def validate(value,legacy):
    """Structural checks only; neither argument can authorize a live execution."""
    if not isinstance(value,dict) or set(value)!={"census","locations"}:raise ValueError("observation fields")
    census=value["census"];old=legacy["census"]
    if not isinstance(census,dict) or set(census)!={"format","module","total","rows"} or type(census["format"]) is not int or census["format"]!=2 or census["module"]!=old["module"] or type(census["total"]) is not int or census["total"]<=0 or census["total"]!=old["total"] or not isinstance(census["rows"],list) or len(census["rows"])!=old["total"]:
        raise ValueError("metadata census identity/count mismatch")
    expected={closure.leaf.kernel.name_key(r["declaration"]):r for r in old["rows"]};seen=set()
    for row in census["rows"]:
        if not isinstance(row,dict) or set(row)!={"declaration","kind","legacy","metadata_v2"}:raise ValueError("metadata row fields")
        key=closure.leaf.kernel.name_key(row["declaration"])
        if key in seen or key not in expected:raise ValueError("duplicate or foreign metadata declaration")
        seen.add(key);original=expected[key]
        if row["kind"]!=original["kind"] or row["legacy"]!={k:v for k,v in original.items() if k not in ("kind","declaration")}:
            raise ValueError("legacy declaration result changed")
        new=row["metadata_v2"]
        if not isinstance(new,dict):raise ValueError("v2 result fields")
        if new.get("status")=="serialized":
            signature=new.get("signature")
            if set(new)!={"status","signature"} or not isinstance(signature,list) or len(signature)!=3 or signature[0]!="declaration-type-with-metadata-v2":raise ValueError("v2 fingerprint domain mismatch")
        elif new.get("status")=="unsupported":
            if set(new)!={"status","reason"} or not isinstance(new["reason"],str) or not new["reason"]:raise ValueError("v2 refusal missing")
        else:raise ValueError("v2 status missing")
        if original["status"]=="serialized":
            old_signature=original["signature"]
            if len(old_signature)!=3 or old_signature[0]!="declaration-type" or new!={"status":"serialized","signature":["declaration-type-with-metadata-v2",*old_signature[1:]]}:
                raise ValueError("metadata-free legacy type changed")
        elif original["reason"]!="expression metadata" and new!=row["legacy"]:
            raise ValueError("nonmetadata legacy refusal changed")
    if seen!=set(expected) or value["locations"]!=legacy["locations"]:raise ValueError("declaration/range coverage drift")
    return {"total":len(seen),"legacy_statuses":dict(Counter(r["legacy"]["status"] for r in census["rows"])),"metadata_v2_statuses":dict(Counter(r["metadata_v2"]["status"] for r in census["rows"]))}


def verify_controls_log(path,steps):
    raw=binder.observer.read_log_bytes(path,binder.expected_log_hash(steps,path))
    if raw.decode().splitlines().count("METADATA_V2_CONTROLS_PASS 14")!=1:
        raise ValueError("metadata separation controls missing")


def verify_scope_artifacts(directory,live,receipt_sha256):
    for path,digest in [(directory/"receipt.json",receipt_sha256),
                        (directory/"metadata.json",live["metadata_sha256"]),
                        (directory/"source-bindings.json",live["bindings_sha256"])]:
        closure.leaf.source_binding.read_bound_json(path,digest)


def run(output):
    """Caller owns the writer lease throughout fresh build and observations."""
    pins=json.loads(PINS.read_text());admitted(pins)
    if not output.is_absolute():raise ValueError("output must be absolute")
    output.mkdir(mode=0o700,exist_ok=False)
    receipt={"schema":1,"kind":"separate-metadata-type-observation-v2","status":"failed","steps":[],"driver_sha256":binder.sha(Path(__file__)),"pins_sha256":binder.sha(PINS)}
    try:
        live=closure.run(output/"scope","scope")
        live_hash=hashlib.sha256((json.dumps(live,indent=2)+"\n").encode()).hexdigest()
        closure.leaf.source_binding.read_bound_json(output/"scope/receipt.json",live_hash)
        legacy=closure.leaf.source_binding.read_bound_json(output/"scope/metadata.json",live["metadata_sha256"])
        compiler_pins=json.loads(binder.PINS.read_text());compiler=binder.check_inputs(compiler_pins)
        original,_=closure.checked_probe(output/"scope/probe.log",binder.expected_log_hash(live["steps"],output/"scope/probe.log"))
        before=binder.observer.capture_environment(original)
        if binder.observer.canonical(before["artifacts"])!=binder.observer.canonical(live["imported_artifacts"]):raise ValueError("Scope artifact drift")
        companions=binder.companion_artifacts(before["artifacts"]);runtime=binder.runtime_files(compiler)
        source_root=output/"sources";source_root.mkdir(mode=0o700);library=output/"extensions";library.mkdir(mode=0o700)
        helper=source_root/HELPER.name;helper.write_bytes(HELPER.read_bytes());helper.chmod(0o444)
        probe=source_root/PROBE.name;probe.write_bytes(PROBE.read_bytes());probe.chmod(0o444)
        if binder.regular(helper)["sha256"]!=pins["helper_sha256"] or binder.regular(probe)["sha256"]!=pins["probe_sha256"]:raise ValueError("staged observation drift")
        env=dict(binder.clean_environment(compiler),LEAN_PATH=str(library)+":"+str(output/"scope/fixtures/compiled"))
        artifact=library/(HELPER.stem+".olean");binder.fresh_output(artifact)
        binder.checked_process([str(compiler),"-j1","--tstack=131072","--root="+str(source_root),"-o",str(artifact),str(helper)],env,output/"helper.log",receipt["steps"])
        verify_controls_log(output/"helper.log",receipt["steps"])
        fresh={"module":[HELPER.stem],"artifact":binder.regular(artifact)}
        extra_companions=binder.companion_artifacts([{"base":{"path":str(artifact)}}]);sidecars=closure.leaf.project_sidecars(artifact)
        log=output/"probe.log";binder.checked_process([str(compiler),"-j1","--tstack=131072","--root="+str(source_root),str(probe)],env,log,receipt["steps"])
        raw=binder.observer.read_log_bytes(log,binder.expected_log_hash(receipt["steps"],log));lines=raw.decode().splitlines()
        env_lines=[x for x in lines if x.startswith(binder.observer.PREFIX)];data=[x for x in lines if x.startswith(PREFIX)]
        if len(lines)!=2 or len(env_lines)!=1 or len(data)!=1:raise ValueError("unexpected observation log")
        observed=binder.observer.json_load(env_lines[0][len(binder.observer.PREFIX):].encode());value=binder.observer.json_load(data[0][len(PREFIX):].encode())
        if binder.observer.name_parts(observed["main_module"])!=(PROBE.stem,):raise ValueError("wrong observation probe")
        after=binder.observer.capture_environment(observed);closure.verify_closure(before["artifacts"],after["artifacts"],[fresh])
        summary=validate(value,legacy)
        if companions!=binder.companion_artifacts(before["artifacts"]) or runtime!=binder.runtime_files(compiler):raise ValueError("runtime/dependency drift")
        if binder.regular(artifact)!=fresh["artifact"] or extra_companions!=binder.companion_artifacts([{"base":{"path":str(artifact)}}]) or sidecars!=closure.leaf.project_sidecars(artifact):raise ValueError("metadata object/companion drift")
        admitted(pins);closure.admitted_sources(json.loads(closure.profile("scope")["pins"].read_text()),"scope");binder.check_inputs(compiler_pins)
        if binder.regular(helper)["sha256"]!=pins["helper_sha256"] or binder.regular(probe)["sha256"]!=pins["probe_sha256"]:raise ValueError("staged observation changed")
        verify_scope_artifacts(output/"scope",live,live_hash)
        binder.verify_process_logs(receipt["steps"]);binder.verify_process_logs(live["steps"])
        child=closure.leaf.source_binding.read_bound_json(output/"scope/fixtures/receipt.json",live["fixture_receipt_sha256"]);binder.verify_process_logs(child["steps"])
        (output/"observation.json").write_text(json.dumps(value,sort_keys=True,indent=2)+"\n")
        receipt.update(status="pass",scope_receipt_sha256=live_hash,helper_artifact=fresh["artifact"],helper_companions=extra_companions,helper_sidecars=sidecars,imported_artifacts=after["artifacts"],observation_sha256=binder.sha(output/"observation.json"),summary=summary,boundary="Separate metadata-preserving v2 observations only. All legacy records/refusals retained. No scanner annotation, equivalence, proof witness, ownership or runtime gate.")
    except Exception as exc:receipt["error"]=str(exc);raise
    finally:(output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--output",type=Path,required=True);args=p.parse_args()
    try:
        with binder.writer_lease():result=run(args.output)
    except (OSError,ValueError,RecursionError,subprocess.SubprocessError) as exc:p.exit(1,"METADATA_OBSERVATION_REJECT: "+str(exc)+"\n")
    print("METADATA_OBSERVATION_PASS "+json.dumps(result["summary"]))


if __name__=="__main__":main()
