#!/usr/bin/env python3
"""Guard cached dependency substitution in real intrinsic-signature observations.

Freshly compile an explicitly admitted unchanged AST or Scope dependency closure.
Exact imported artifact identities, metadata and direct source ranges are checked.
No arbitrary manifest, held workload, live ownership or full project claim.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

import bind_project_leaf as leaf
binder=leaf.binder
PINS=binder.FIXTURES/"project-closure-pins.json"
PROBE=binder.FIXTURES/"ASTSourceBinding.lean"
MODULE=["str",["str",["anonymous"],"Solidity"],"AST"]
EXPECTED=[("Solidity/KeySort.lean",["Solidity","KeySort"],[]),
          ("Solidity/AST.lean",["Solidity","AST"],["Solidity/KeySort.lean"])]
IMPORTS={"Solidity/KeySort.lean":[],"Solidity/AST.lean":["Lean.Elab.Tactic","Lean.Elab.Deriving","Solidity.KeySort"]}


def encoded(parts):
    value=["anonymous"]
    for part in parts:value=["str",value,part]
    return value


def profile(target):
    """Keep admitted source closures explicit; arbitrary manifests are forbidden."""
    if target=="ast":
        return {"pins":PINS,"probe":PROBE,"module":MODULE,"expected":EXPECTED,"imports":IMPORTS}
    if target=="scope":
        return {"pins":binder.FIXTURES/"scope-closure-pins.json","probe":binder.FIXTURES/"ScopeSourceBinding.lean",
                "module":encoded(["Solidity","Scope"]),
                "expected":EXPECTED+[("Solidity/Scope.lean",["Solidity","Scope"],["Solidity/AST.lean"])],
                "imports":IMPORTS|{"Solidity/Scope.lean":["Solidity.AST"]}}
    raise ValueError("unadmitted project target")


def admitted_sources(pins, target="ast"):
    selected=profile(target)
    rows=pins["modules"]
    if pins.get("schema")!=1 or [(r["path"],r["module"],r["project_dependencies"]) for r in rows]!=selected["expected"]:
        raise ValueError("unadmitted project closure or dependency order")
    if binder.sha(binder.PINS)!=pins["fixture_contract_sha256"] or binder.regular(selected["probe"])["sha256"]!=pins["probe_sha256"]:
        raise ValueError("closure probe/fixture contract drift")
    for row in rows:
        source=binder.ROOT/row["path"]
        if binder.regular(source)["sha256"]!=row["sha256"]:raise ValueError("closure source pin drift")
        text=binder.scanner.hide_strings(binder.scanner.mask(source.read_text()))
        imports=re.findall(r"(?m)^\s*(?:(?:public|meta)\s+)*import\s+([^\n]+)",text)
        if [i.strip() for i in imports]!=selected["imports"][row["path"]]:raise ValueError("unadmitted source imports")


def verify_closure(before,after,fresh):
    old,new=leaf.artifact_map(before),leaf.artifact_map(after)
    wanted={leaf.kernel.name_key(encoded(r["module"])):r["artifact"] for r in fresh}
    if len(wanted)!=len(fresh) or set(wanted)&set(old) or set(new)!=set(old)|set(wanted):
        raise ValueError("unexpected fresh project dependency closure")
    for name,row in old.items():
        if binder.observer.canonical(new[name])!=binder.observer.canonical(row):raise ValueError("existing dependency changed")
    for name,artifact in wanted.items():
        if any(new[name]["base"][k]!=artifact[k] for k in ("sha256","realpath")):
            raise ValueError("project dependency is not the fresh compiled object")


def staged_bytes(source_root,row):
    raw=(source_root/row["path"]).read_bytes()
    if hashlib.sha256(raw).hexdigest()!=row["sha256"]:raise ValueError("staged lexical bytes differ from compiled source pin")
    return raw


def checked_probe(log,expected_sha):
    raw=binder.observer.read_log_bytes(log,expected_sha)
    lines=raw.decode().splitlines()
    env=[x for x in lines if x.startswith(binder.observer.PREFIX)]
    records=[x for x in lines if x.startswith(leaf.PREFIX)]
    if len(env)!=1 or len(records)!=1 or len(lines)!=2:raise ValueError("unexpected project probe log lines")
    record=binder.observer.json_load(records[0][len(leaf.PREFIX):].encode())
    if not isinstance(record,dict) or set(record)!={"census","locations"}:raise ValueError("project probe fields")
    return binder.observer.json_load(env[0][len(binder.observer.PREFIX):].encode()),record


def run(output, target="ast"):
    """Caller owns writer lease for the complete fresh build and observation."""
    selected=profile(target);pins_path=selected["pins"];probe_input=selected["probe"];target_module=selected["module"]
    pins=json.loads(pins_path.read_text());admitted_sources(pins,target)
    if not output.is_absolute():raise ValueError("output must be absolute")
    output.mkdir(mode=0o700,exist_ok=False)
    receipt={"schema":1,"kind":"trusted-live-project-closure-binding","status":"failed","steps":[],
             "driver_sha256":binder.sha(Path(__file__)),"pins_sha256":binder.sha(pins_path)}
    try:
        live=binder.rebuild(output/"fixtures")
        live_hash=hashlib.sha256((json.dumps(live,indent=2)+"\n").encode()).hexdigest()
        leaf.source_binding.read_bound_json(output/"fixtures/receipt.json",live_hash)
        compiler_pins=json.loads(binder.PINS.read_text());compiler=binder.check_inputs(compiler_pins)
        original,_,_=binder.observer.read_log(output/"fixtures/logs/consumer.log",binder.expected_log_hash(live["steps"],output/"fixtures/logs/consumer.log"))
        before=binder.observer.capture_environment(original)
        if binder.observer.canonical(before["artifacts"])!=binder.observer.canonical(live["compiled_artifacts"]):raise ValueError("fixture closure drift")
        companions=binder.companion_artifacts(before["artifacts"]);runtime=binder.runtime_files(compiler)
        source_root=output/"sources";source_root.mkdir(mode=0o700)
        library=output/"fixtures/compiled";env=dict(binder.clean_environment(compiler),LEAN_PATH=str(library))
        fresh=[]
        for row in pins["modules"]:
            staged=source_root/row["path"];staged.parent.mkdir(mode=0o700,parents=True,exist_ok=True)
            raw=(binder.ROOT/row["path"]).read_bytes();staged.write_bytes(raw);staged.chmod(0o444)
            if binder.regular(staged)["sha256"]!=row["sha256"]:raise ValueError("staged project source drift")
            artifact=library/Path(row["path"]).with_suffix(".olean");artifact.parent.mkdir(mode=0o700,parents=True,exist_ok=True);binder.fresh_output(artifact)
            binder.checked_process([str(compiler),"-j1","--tstack=131072","--root="+str(source_root),"-o",str(artifact),str(staged)],env,output/(row["module"][-1]+".log"),receipt["steps"])
            observed=binder.regular(artifact)
            if not observed["size"]:raise ValueError("empty project compiler output")
            fresh.append({"module":row["module"],"source":row["path"],"source_sha256":row["sha256"],"artifact":observed,
                          "companions":binder.companion_artifacts([{"base":{"path":str(artifact)}}]),"sidecars":leaf.project_sidecars(artifact)})
        probe=source_root/probe_input.name;probe.write_bytes(probe_input.read_bytes());probe.chmod(0o444)
        if binder.regular(probe)["sha256"]!=pins["probe_sha256"]:raise ValueError("staged probe drift")
        log=output/"probe.log"
        binder.checked_process([str(compiler),"-j1","--tstack=131072","--root="+str(source_root),str(probe)],env,log,receipt["steps"])
        probe_log_sha=receipt["steps"][-1]["log_sha256"]
        observed,record=checked_probe(log,probe_log_sha)
        if binder.observer.name_parts(observed["main_module"])!=(probe_input.stem,):raise ValueError("wrong closure probe module")
        after=binder.observer.capture_environment(observed);verify_closure(before["artifacts"],after["artifacts"],fresh)
        if companions!=binder.companion_artifacts(before["artifacts"]) or runtime!=binder.runtime_files(compiler):raise ValueError("runtime/SDK companion drift")
        for row in fresh:
            artifact=Path(row["artifact"]["path"])
            if binder.regular(artifact)!=row["artifact"] or binder.companion_artifacts([{"base":{"path":str(artifact)}}])!=row["companions"] or leaf.project_sidecars(artifact)!=row["sidecars"]:
                raise ValueError("fresh project artifact/companion drift")
            if binder.regular(source_root/row["source"])["sha256"]!=row["source_sha256"]:raise ValueError("staged source changed")
        leaf.kernel.validate(record["census"],target_module)
        source=binder.ROOT/pins["modules"][-1]["path"];raw=staged_bytes(source_root,pins["modules"][-1])
        joined=leaf.source_binding.join_locations(raw.decode(),binder.scanner.scan(source,binder.ROOT,raw),record["census"],record["locations"],target_module)
        if binder.sha(log)!=probe_log_sha:raise ValueError("probe log changed after parsing")
        admitted_sources(pins,target);binder.check_inputs(compiler_pins)
        if binder.regular(probe)["sha256"]!=pins["probe_sha256"]:raise ValueError("staged probe changed")
        leaf.source_binding.read_bound_json(output/"fixtures/receipt.json",live_hash)
        binder.verify_process_logs(receipt["steps"]); binder.verify_process_logs(live["steps"])
        (output/"metadata.json").write_text(json.dumps(record,sort_keys=True,indent=2)+"\n")
        (output/"source-bindings.json").write_text(json.dumps(joined,sort_keys=True,indent=2)+"\n")
        receipt.update(status="pass",keysort_gate="pass",fixture_receipt_sha256=live_hash,fresh_project_closure=fresh,
                       imported_artifacts=after["artifacts"],metadata_sha256=binder.sha(output/"metadata.json"),bindings_sha256=binder.sha(output/"source-bindings.json"),
                       lexical_total=joined["lexical_total"],linked=joined["linked"],unresolved=joined["unresolved"],visible_kernel_total=joined["visible_kernel_total"],
                       boundary=("Fresh unchanged AST intrinsic types/direct source ranges plus exact fresh KeySort dependency. Visible imports only; no general/private/unloaded/body-equivalence or ownership claim; no runtime/model gate or timing clearance." if target=="ast" else "Fresh unchanged Scope intrinsic types/direct ranges plus exact fresh AST and KeySort dependencies. Visible imports only; no general/private/unloaded/body-equivalence or ownership claim; no runtime/model gate or timing clearance."))
    except Exception as exc:receipt["error"]=str(exc);raise
    finally:(output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--output",type=Path,required=True);p.add_argument("--target",choices=("ast","scope"),default="ast");args=p.parse_args()
    try:
        with binder.writer_lease():r=run(args.output,args.target)
    except (OSError,ValueError,RecursionError,subprocess.SubprocessError) as exc:p.exit(1,"PROJECT_CLOSURE_REJECT: "+str(exc)+"\n")
    print("KEYSORT_COMPILE_PASS; LOCAL_PROJECT_CLOSURE_BINDING_PASS "+json.dumps({k:r[k] for k in ("lexical_total","linked","unresolved","visible_kernel_total")}))


if __name__=="__main__":main()
