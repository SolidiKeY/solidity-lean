#!/usr/bin/env python3
"""Guard fixture-only provenance being promoted to real project declarations.

The only admitted project source is the pinned, import-free Solidity.KeySort.
It is copied unchanged and compiled fresh before an isolated metadata probe.
Other project dependencies, cached artifacts and saved receipts cannot satisfy
this producer. No general/private/unloaded coverage or ownership claim follows.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import bind_signature_fixture as binder
import bind_source_locations as source_binding
import census_fixture_kernel as kernel

PINS = binder.FIXTURES / "project-leaf-pins.json"
MODULE = ["str",["str",["anonymous"],"Solidity"],"KeySort"]
PREFIX = "H62_PROJECT_BINDING "
SOURCE = binder.ROOT / "Solidity/KeySort.lean"
PROBE = binder.FIXTURES / "KeySortSourceBinding.lean"


def admitted_sources(pins):
    if binder.regular(SOURCE)["sha256"] != pins["source_sha256"]:
        raise ValueError("project source pin drift")
    if binder.regular(PROBE)["sha256"] != pins["probe_sha256"]:
        raise ValueError("project probe pin drift")
    if binder.sha(binder.PINS) != pins["fixture_contract_sha256"]:
        raise ValueError("fixture rebuild contract drift")
    text = binder.scanner.hide_strings(binder.scanner.mask(SOURCE.read_text()))
    if __import__("re").search(r"(?m)^\s*(?:(?:public|meta)\s+)*import\b",text):
        raise ValueError("project leaf is no longer import-free")


def read_log(path, expected_sha256=None):
    raw = binder.observer.read_log_bytes(path, expected_sha256)
    lines=raw.decode().splitlines()
    env=[x for x in lines if x.startswith(binder.observer.PREFIX)]
    records=[x for x in lines if x.startswith(PREFIX)]
    if len(env)!=1 or len(records)!=1 or len(lines)!=2:raise ValueError("unexpected project probe log lines")
    record=binder.observer.json_load(records[0][len(PREFIX):].encode())
    if not isinstance(record,dict) or set(record)!={"census","locations"}:raise ValueError("project probe fields")
    return binder.observer.json_load(env[0][len(binder.observer.PREFIX):].encode()),record


def artifact_map(rows):
    result={}
    for row in rows:
        key=kernel.name_key(row["module"])
        if key in result:raise ValueError("duplicate imported artifact")
        result[key]=row
    return result


def verify_closure(before,after,project_artifact):
    old,new=artifact_map(before),artifact_map(after);target=kernel.name_key(MODULE)
    if target in old or set(new)!=set(old)|{target}:raise ValueError("unexpected project dependency closure")
    if any(binder.observer.canonical(new[name])!=binder.observer.canonical(row) for name,row in old.items()):
        raise ValueError("existing dependency changed during project probe")
    if new[target]["base"]["sha256"]!=project_artifact["sha256"] or new[target]["base"]["realpath"]!=project_artifact["realpath"]:
        raise ValueError("project artifact not the fresh compiled object")


def project_sidecars(artifact):
    result=[]
    for suffix in (".server",".private"):
        path=Path(str(artifact)+suffix)
        try:path.lstat()
        except FileNotFoundError:result.append({"path":str(path),"present":False});continue
        result.append({"present":True,**binder.regular(path)})
    return result


def run(output):
    """Caller holds writer lease across fresh compilation and all observations."""
    pins=json.loads(PINS.read_text());admitted_sources(pins)
    if not output.is_absolute():raise ValueError("project output must be absolute")
    output.mkdir(mode=0o700,exist_ok=False)
    receipt={"schema":1,"kind":"trusted-live-project-leaf-binding","status":"failed","steps":[],
             "driver_sha256":binder.sha(Path(__file__)),"pins_sha256":binder.sha(PINS),
             "source_sha256":pins["source_sha256"],"probe_sha256":pins["probe_sha256"]}
    try:
        live=binder.rebuild(output/"fixtures")
        live_hash=hashlib.sha256((json.dumps(live,indent=2)+"\n").encode()).hexdigest()
        source_binding.read_bound_json(output/"fixtures/receipt.json",live_hash)
        receipt["fixture_receipt_sha256"]=live_hash
        compiler_pins=json.loads(binder.PINS.read_text());compiler=binder.check_inputs(compiler_pins)
        original,_,_=binder.observer.read_log(output/"fixtures/logs/consumer.log",binder.expected_log_hash(live["steps"],output/"fixtures/logs/consumer.log"))
        before=binder.observer.capture_environment(original)
        if binder.observer.canonical(before["artifacts"])!=binder.observer.canonical(live["compiled_artifacts"]):
            raise ValueError("fixture artifacts changed before project compile")
        companions=binder.companion_artifacts(before["artifacts"]);runtime=binder.runtime_files(compiler)
        source_root=output/"sources";(source_root/"Solidity").mkdir(parents=True,mode=0o700)
        staged=source_root/"Solidity/KeySort.lean";raw=SOURCE.read_bytes();staged.write_bytes(raw);staged.chmod(0o444)
        probe=source_root/PROBE.name;probe.write_bytes(PROBE.read_bytes());probe.chmod(0o444)
        if hashlib.sha256(raw).hexdigest()!=pins["source_sha256"] or binder.regular(staged)["sha256"]!=pins["source_sha256"] or binder.regular(probe)["sha256"]!=pins["probe_sha256"]:
            raise ValueError("staged project source/probe mismatch")
        library=output/"fixtures/compiled";(library/"Solidity").mkdir(mode=0o700)
        artifact=library/"Solidity/KeySort.olean";binder.fresh_output(artifact)
        env=dict(binder.clean_environment(compiler),LEAN_PATH=str(library))
        command=[str(compiler),"-j1","--tstack=131072","--root="+str(source_root),"-o",str(artifact),str(staged)]
        binder.checked_process(command,env,output/"keysort.log",receipt["steps"])
        project_artifact=binder.regular(artifact)
        if not project_artifact["size"]:raise ValueError("empty project compiler output")
        project_companions=binder.companion_artifacts([{"base":{"path":str(artifact)}}])
        sidecars=project_sidecars(artifact)
        log=output/"probe.log"
        binder.checked_process([str(compiler),"-j1","--tstack=131072","--root="+str(source_root),str(probe)],env,log,receipt["steps"])
        observed,record=read_log(log,binder.expected_log_hash(receipt["steps"],log))
        if binder.observer.name_parts(observed["main_module"])!=("KeySortSourceBinding",):raise ValueError("wrong project probe module")
        after=binder.observer.capture_environment(observed);verify_closure(before["artifacts"],after["artifacts"],project_artifact)
        if runtime!=binder.runtime_files(compiler) or companions!=binder.companion_artifacts(before["artifacts"]):raise ValueError("project runtime/companion drift")
        if project_companions!=binder.companion_artifacts([{"base":{"path":str(artifact)}}]) or sidecars!=project_sidecars(artifact):raise ValueError("project companion/sidecar drift")
        kernel.validate(record["census"],MODULE)
        lexical=binder.scanner.scan(SOURCE,binder.ROOT,raw)
        joined=source_binding.join_locations(raw.decode(),lexical,record["census"],record["locations"],MODULE)
        admitted_sources(pins);binder.check_inputs(compiler_pins)
        source_binding.read_bound_json(output/"fixtures/receipt.json",live_hash)
        if binder.regular(staged)["sha256"]!=pins["source_sha256"] or binder.regular(probe)["sha256"]!=pins["probe_sha256"] or binder.regular(artifact)!=project_artifact:
            raise ValueError("staged project source/artifact drift")
        binder.verify_process_logs(receipt["steps"]); binder.verify_process_logs(live["steps"])
        (output/"metadata.json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n")
        (output/"source-bindings.json").write_text(json.dumps(joined,sort_keys=True,indent=2)+"\n")
        receipt.update(status="pass",keysort_gate="pass",project_artifact=project_artifact,
                       project_companions=project_companions,project_sidecars=sidecars,
                       imported_artifacts=after["artifacts"],metadata_sha256=binder.sha(output/"metadata.json"),
                       bindings_sha256=binder.sha(output/"source-bindings.json"),lexical_total=joined["lexical_total"],
                       linked=joined["linked"],unresolved=joined["unresolved"],visible_kernel_total=joined["visible_kernel_total"],
                       boundary="Fresh unchanged KeySort source/name/type linkage and bounded compile only; no general project, ownership, private/unloaded or body-equivalence claim. No full runtime/model gate.")
    except Exception as exc:receipt["error"]=str(exc);raise
    finally:(output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--output",type=Path,required=True);a=p.parse_args()
    try:
        with binder.writer_lease():r=run(a.output)
    except (OSError,ValueError,RecursionError,subprocess.SubprocessError) as exc:p.exit(1,"PROJECT_BINDING_REJECT: "+str(exc)+"\n")
    print("KEYSORT_COMPILE_PASS; LOCAL_PROJECT_BINDING_PASS "+json.dumps({k:r[k] for k in ("lexical_total","linked","unresolved","visible_kernel_total")}))


if __name__=="__main__":main()
