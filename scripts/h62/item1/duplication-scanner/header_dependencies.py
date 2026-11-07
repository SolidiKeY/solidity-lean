#!/usr/bin/env python3
"""Guard guessed import graphs and accidental loading of held project code.

Compiler header parsing treats captured tracked core sources as inert strings.
No inventoried project imports or bodies execute. Declared paths, missing/shadowed inputs,
and header failures remain observations, never compilation/ownership grants.
"""
import argparse
from collections import Counter, deque
import fnmatch
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import subprocess
import tomllib

import bind_signature_fixture as binder
import bind_source_locations as binding

ROOT=binder.ROOT
BASE="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
MAP="docs/module-map/readonly-calls.md"
HELD="Solidity/Backend/WorldCalls/Premises.lean"
PROBE=binder.FIXTURES/"HeaderImports.lean"
CONTROLS=binder.FIXTURES/"header-controls.json"
PINS=binder.FIXTURES/"header-dependency-pins.json"
MAX_LOG=128*1024**2


def git(*args):return subprocess.check_output(["git",*args],cwd=ROOT)


def encoded(parts):
    result=["anonymous"]
    for part in parts:result=["str",result,part]
    return result


def module_key(value):return binder.observer.name_parts(value)


def frozen_targets():
    import re
    raw=git("show",BASE+":"+MAP);files=set(git("ls-tree","-r","--name-only",BASE).decode().splitlines())
    paths=set();parent=None
    for spec in re.findall(r"`([^`]+\.lean)`",raw.decode()):
        pattern=(str(parent/spec) if "/" not in spec and parent is not None else "Solidity/"+spec)
        if "**" in pattern:raise ValueError("unsupported frozen recursive map pattern")
        parts=PurePosixPath(pattern).parts
        matched=[f for f in files if len(PurePosixPath(f).parts)==len(parts) and all(fnmatch.fnmatchcase(a,b) for a,b in zip(PurePosixPath(f).parts,parts))]
        if not matched:raise ValueError("unresolved frozen map entry: "+spec)
        paths.update(matched);parent=PurePosixPath(pattern).parent
    if len(paths)!=129:raise ValueError("frozen file census drift")
    return sorted(paths),hashlib.sha256(raw).hexdigest()


def source_roots(config):
    if PurePosixPath(config.get("srcDir","."))!=PurePosixPath("."):raise ValueError("unsupported non-default core package source root")
    roots=set()
    for lib in config.get("lean_lib",[]):
        folder=lib.get("srcDir",".")
        path=PurePosixPath(folder)
        if path==PurePosixPath("."):continue
        if path.is_absolute() or ".." in path.parts:raise ValueError("unsafe core source root")
        if path==PurePosixPath("Solidity") or path.is_relative_to("Solidity"):raise ValueError("overlapping primary source root")
        roots.add(path)
    values=sorted(roots)
    for i,left in enumerate(values):
        for right in values[i+1:]:
            if left.is_relative_to(right) or right.is_relative_to(left):raise ValueError("overlapping configured source roots")
    return values


def blob_hash(raw):
    return subprocess.check_output(["git","hash-object","--stdin"],cwd=ROOT,input=raw).decode().strip()


def collect_sources(source_head):
    config_raw=(ROOT/"lakefile.toml").read_bytes()
    config_blob=git("rev-parse",source_head+":lakefile.toml").decode().strip()
    if blob_hash(config_raw)!=config_blob:raise ValueError("core configuration differs from captured tree")
    config=tomllib.loads(config_raw.decode());extra=source_roots(config)
    nodes=[];inputs=[];excluded=0
    for entry in git("ls-tree","-rz",source_head).split(b"\0"):
        if not entry:continue
        meta,name=entry.split(b"\t",1);mode,kind,blob=meta.decode().split();path=name.decode()
        if not path.endswith(".lean"):continue
        relative=None
        for folder in extra:
            if PurePosixPath(path).is_relative_to(folder):relative=PurePosixPath(path).relative_to(folder)
        if relative is None and (path.startswith("Solidity/") or "/" not in path):relative=PurePosixPath(path)
        if relative is None:excluded+=1;continue
        module=encoded(relative.with_suffix("").parts)
        node={"path":path,"module":module,"git_blob":blob,"status":"source-error","imports":[],
              "body_parsed":False,"dynamic_references_known":False,"ownership_verified":False}
        try:
            file=ROOT/path
            if mode not in ("100644","100755") or not stat.S_ISREG(file.lstat().st_mode) or file.resolve(strict=True)!=file:raise ValueError("nonregular/alias source")
            raw=file.read_bytes()
            if len(raw)>64*1024**2:raise ValueError("source exceeds file byte limit")
        except (OSError,ValueError) as exc:node["error"]=str(exc)
        else:
            # Hash the captured bytes, not a later reread.
            actual=blob_hash(raw)
            node["source_sha256"]=hashlib.sha256(raw).hexdigest()
            if actual!=blob:node["error"]="working-tree source drift"
            else:
                try:source=raw.decode("utf-8")
                except UnicodeError:node["error"]="invalid UTF-8 source"
                else:
                    node["status"]="captured-source";inputs.append({"path":path,"source":source})
        nodes.append(node)
    return nodes,inputs,{"config_sha256":hashlib.sha256(config_raw).hexdigest(),"config_git_blob":config_blob,"source_head":source_head,"additional_core_roots":[str(x) for x in extra],"excluded_tracked_Lean_files":excluded,"scope":"tracked Solidity, top-level and configured additional core roots only; root tests and separate-package paths outside those roots excluded; registration not established"}


def validate_headers(nodes,inputs,records):
    by_path={x["path"]:x for x in inputs}
    parsed={x["path"]:x for x in records}
    if len(parsed)!=len(records) or set(parsed)!=set(by_path):raise ValueError("header record coverage mismatch")
    for path,row in parsed.items():
        if (set(row)!={"path","status","header_prefix","is_module","imports","diagnostics","body_parsed","dynamic_references_known"}
            or row["status"] not in ("parsed-header","header-error") or row["body_parsed"] is not False or row["dynamic_references_known"] is not False
            or not isinstance(row["header_prefix"],str) or not by_path[path]["source"].startswith(row["header_prefix"])
            or not isinstance(row["imports"],list) or not isinstance(row["diagnostics"],list)
            or any(not isinstance(message,str) for message in row["diagnostics"])):
            raise ValueError("malformed/unbound header record")
        if row["status"]=="parsed-header" and type(row["is_module"]) is not bool:raise ValueError("header module flag")
        if row["status"]=="header-error" and (row["is_module"] is not None or row["imports"] or not row["diagnostics"]):raise ValueError("header failure hidden")
        for item in row["imports"]:
            if set(item)!={"module","importAll","isExported","isMeta","implicit"} or any(type(item[k]) is not bool for k in ("importAll","isExported","isMeta","implicit")):
                raise ValueError("malformed import flags")
    for node in nodes:
        if node["path"] not in parsed:continue
        row=parsed[node["path"]]
        node.update({k:row[k] for k in ("status","imports","diagnostics","is_module")})
        node["header_sha256"]=hashlib.sha256(row["header_prefix"].encode()).hexdigest()


def resolve(nodes,toolchain):
    index={};sdk={}
    for node in nodes:index.setdefault(module_key(node["module"]),[]).append(node["path"])
    for node in nodes:
        for item in node["imports"]:
            try:parts=module_key(item["module"])
            except ValueError as exc:item["resolution"]={"status":"unsafe-or-unsupported-module-name","error":str(exc)};continue
            if not parts:item["resolution"]={"status":"anonymous-module"};continue
            candidates=index.get(parts,[]);sdk_path=Path(str(toolchain/"lib/lean"/Path(*parts))+".olean")
            present=sdk_path.is_file()
            if len(candidates)>1 or (candidates and present):item["resolution"]={"status":"ambiguous-source-or-sdk","candidates":candidates}
            elif candidates:item["resolution"]={"status":"project-source","path":candidates[0]}
            elif present:
                if not sdk_path.resolve().is_relative_to(toolchain/"lib/lean"):item["resolution"]={"status":"sdk-path-escape"};continue
                if parts not in sdk:sdk[parts]=binder.observer.regular_hash(sdk_path)
                item["resolution"]={"status":"sdk-artifact-observed-not-loaded","artifact_sha256":sdk[parts]["sha256"],"path":str(sdk_path)}
            else:item["resolution"]={"status":"unresolved-module"}
    return sdk


def held_path(nodes,target,held=HELD):
    index={n["path"]:n for n in nodes};queue=deque([(target,[target])]);seen=set();unknown=[]
    while queue:
        current,path=queue.popleft()
        if current==held:return {"status":"declared-path-to-held-module","path":path,"unknown":unknown}
        if current in seen:continue
        seen.add(current);node=index.get(current)
        if node is None or node["status"]!="parsed-header":unknown.append(current);continue
        for item in node["imports"]:
            resolution=item["resolution"]
            if resolution["status"]=="project-source":queue.append((resolution["path"],path+[resolution["path"]]))
            elif resolution["status"]!="sdk-artifact-observed-not-loaded":unknown.append(current+":"+json.dumps(item["module"]))
    return {"status":"header-dependency-unknown" if unknown else "no-declared-path-to-held-module","path":None,"unknown":sorted(set(unknown))}


def target_records(nodes, targets):
    """Keep target identity distinct from the optional dependency path."""
    if len(set(targets)) != len(targets):
        raise ValueError("duplicate target identity")
    return [{"target": target, **held_path(nodes, target)} for target in targets]


def control_inputs(output):
    values=json.loads(CONTROLS.read_text())["cases"]
    return values,[{"path":"@control/"+case["id"],"source":case["source"].replace("__MARKER__",json.dumps(str(output/"CONTROL-MUST-NOT-EXECUTE")))} for case in values]


def verify_controls(cases,records,output):
    index={row["path"]:row for row in records};results=[]
    for case in cases:
        row=index.get("@control/"+case["id"])
        if not row or row["status"]!=case["status"] or [list(module_key(x["module"])) for x in row["imports"]]!=case["modules"]:
            raise ValueError("compiler header control failed: "+case["id"])
        if "flags" in case and [[x[k] for k in ("importAll","isExported","isMeta","implicit")] for x in row["imports"]]!=case["flags"]:
            raise ValueError("compiler header import flags failed: "+case["id"])
        if row["body_parsed"] is not False or row["dynamic_references_known"] is not False:
            raise ValueError("control body/dynamic claim")
        results.append({"id":case["id"],"status":"pass"})
    if (output/"CONTROL-MUST-NOT-EXECUTE").exists():raise ValueError("inventoried body was executed")
    return results


def run(output):
    pins=json.loads(PINS.read_text())
    if binder.regular(PROBE)["sha256"]!=pins["probe_sha256"] or binder.sha(binder.PINS)!=pins["fixture_contract_sha256"] or binder.sha(CONTROLS)!=pins["controls_sha256"]:raise ValueError("header parser contract drift")
    if not output.is_absolute():raise ValueError("output must be absolute")
    output.mkdir(mode=0o700,exist_ok=False);receipt={"schema":1,"status":"failed","steps":[],"driver_sha256":binder.sha(Path(__file__)),"pins_sha256":binder.sha(PINS)}
    try:
        source_head=git("rev-parse","HEAD").decode().strip()
        nodes,inputs,scope=collect_sources(source_head);targets,map_hash=frozen_targets()
        cases,control_rows=control_inputs(output)
        all_inputs=inputs+control_rows
        data=output/"sources.jsonl"
        with data.open("w") as stream:
            for row in all_inputs:stream.write(json.dumps(row,ensure_ascii=False)+"\n")
        data.chmod(0o444);input_hash=binder.sha(data)
        live=binder.rebuild(output/"fixtures");live_hash=hashlib.sha256((json.dumps(live,indent=2)+"\n").encode()).hexdigest();binding.read_bound_json(output/"fixtures/receipt.json",live_hash)
        compiler_pins=json.loads(binder.PINS.read_text());compiler=binder.check_inputs(compiler_pins)
        old,_,_=binder.observer.read_log(output/"fixtures/logs/consumer.log",binder.expected_log_hash(live["steps"],output/"fixtures/logs/consumer.log"));before=binder.observer.capture_environment(old)
        if binder.observer.canonical(before["artifacts"])!=binder.observer.canonical(live["compiled_artifacts"]):raise ValueError("fixture artifact drift")
        runtime=binder.runtime_files(compiler);companions=binder.companion_artifacts(before["artifacts"])
        staged=output/PROBE.name;staged.write_bytes(PROBE.read_bytes());staged.chmod(0o444)
        if binder.regular(staged)["sha256"]!=pins["probe_sha256"]:raise ValueError("staged parser drift")
        env=dict(binder.clean_environment(compiler),LEAN_PATH=str(output/"fixtures/compiled"));log=output/"headers.log"
        binder.checked_process([str(compiler),"-j1","--tstack=131072","--root="+str(output),"--run",str(staged),str(data)],env,log,receipt["steps"])
        records=[];observed=None;summary=None
        if binder.regular(log)["sha256"]!=receipt["steps"][-1]["log_sha256"]:raise ValueError("parser log artifact changed")
        raw_log=binder.observer.read_log_bytes(log,binder.expected_log_hash(receipt["steps"],log),max_bytes=MAX_LOG)
        for line in raw_log.decode().splitlines():
            if line.startswith(binder.observer.PREFIX):
                if observed is not None:raise ValueError("duplicate parser environment")
                observed=binder.observer.json_load(line[len(binder.observer.PREFIX):].encode())
            elif line.startswith("H62_HEADER_RECORD "):records.append(binder.observer.json_load(line[len("H62_HEADER_RECORD "):].encode()))
            elif line.startswith("H62_IMPORT_INVENTORY "):
                if summary is not None:raise ValueError("duplicate parser summary")
                summary=binder.observer.json_load(line[len("H62_IMPORT_INVENTORY "):].encode())
            else:raise ValueError("unexpected parser output")
        if summary!={"format":1,"lean_version":"4.24.0","records":len(all_inputs)} or observed is None:raise ValueError("parser summary/coverage mismatch")
        a,b=dict(old),dict(observed);a.pop("main_module");main=b.pop("main_module")
        if binder.observer.name_parts(main)!=("HeaderImports",) or binder.observer.canonical(a)!=binder.observer.canonical(b):raise ValueError("parser loaded unexpected dependency environment")
        after=binder.observer.capture_environment(observed)
        if binder.observer.canonical(before["artifacts"])!=binder.observer.canonical(after["artifacts"]) or runtime!=binder.runtime_files(compiler) or companions!=binder.companion_artifacts(after["artifacts"]):raise ValueError("parser runtime/artifact drift")
        if binder.sha(data)!=input_hash or binder.regular(staged)["sha256"]!=pins["probe_sha256"] or binder.regular(PROBE)["sha256"]!=pins["probe_sha256"]:raise ValueError("parser/input drift")
        for node in nodes:
            if "source_sha256" in node and hashlib.sha256((ROOT/node["path"]).read_bytes()).hexdigest()!=node["source_sha256"]:raise ValueError("inventoried source changed")
        validate_headers(nodes,all_inputs,records)
        control_results=verify_controls(cases,records,output)
        sdk=resolve(nodes,compiler.parent.parent)
        target_rows=target_records(nodes,targets)
        report={"schema":1,"source_head":source_head,"original_base":BASE,"controls":control_results,"kind":"compiler-parsed-declared-header-dependency-inventory","scope":scope,"nodes":nodes,"sdk_artifacts_observed_not_loaded":[sdk[k] for k in sorted(sdk)],"frozen_map_sha256":map_hash,"original_obligations":792,"frozen_target_files":129,"targets":target_rows,"target_statuses":dict(Counter(r["status"] for r in target_rows)),"node_statuses":dict(Counter(n["status"] for n in nodes)),"held_module":HELD,"boundary":"Headers only. No inventoried project imports/bodies executed, no compilation permission, dynamic/private/body coverage, signature/artifact source binding or ownership. No-path is not clearance of any timing hold."}
        (output/"inventory.json").write_text(json.dumps(report,sort_keys=True,indent=2)+"\n")
        binder.check_inputs(compiler_pins);binding.read_bound_json(output/"fixtures/receipt.json",live_hash)
        if binder.regular(log)["sha256"]!=receipt["steps"][-1]["log_sha256"] or binder.sha(CONTROLS)!=pins["controls_sha256"]:raise ValueError("parser log/control drift")
        if git("rev-parse","HEAD").decode().strip()!=source_head or hashlib.sha256((ROOT/"lakefile.toml").read_bytes()).hexdigest()!=scope["config_sha256"]:raise ValueError("source head/config changed during inventory")
        binder.verify_process_logs(receipt["steps"]); binder.verify_process_logs(live["steps"])
        receipt.update(status="pass",input_sha256=input_hash,fixture_receipt_sha256=live_hash,inventory_sha256=binder.sha(output/"inventory.json"),nodes=len(nodes),parsed=len(records)-len(cases),controls=control_results,target_statuses=report["target_statuses"],node_statuses=report["node_statuses"],inventoried_body_execution=False,inventoried_project_modules_loaded=False)
    except Exception as exc:receipt["error"]=str(exc);raise
    finally:(output/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--output",type=Path,required=True);args=p.parse_args()
    try:
        with binder.writer_lease():result=run(args.output)
    except (OSError,ValueError,RecursionError,subprocess.SubprocessError) as exc:p.exit(1,"HEADER_INVENTORY_REJECT: "+str(exc)+"\n")
    print("HEADER_INVENTORY_CAPTURE_PASS "+json.dumps({k:result[k] for k in ("nodes","parsed","node_statuses","target_statuses")}))


if __name__=="__main__":main()
