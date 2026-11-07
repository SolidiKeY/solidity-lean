#!/usr/bin/env python3
"""Portable paired-context evidence; integrity checks do not rerun Lean's kernel.
Blobs are content-addressed. Absolute receipt paths remain provenance only: verify
uses solely the archive, never the original VM paths. Original/current proofs
are kept separate and no definition-equivalence or operational refusal is claimed.
"""
import argparse,gzip,hashlib,io,json,re,subprocess,tarfile
from collections import Counter
from pathlib import Path
from census import ROOT,mask,module_to_path,scan
ALLOW={"propext","Classical.choice","Quot.sound"}
def h(data):return hashlib.sha256(data).hexdigest()
def canonical(obj):return(json.dumps(obj,sort_keys=True,separators=(",",":"))+"\n").encode()
def export(a):
    output=a.out.resolve();assert not output.is_relative_to(ROOT)
    providers={};sizes={}
    def blob(path):
        data=path.read_bytes();key=h(data);providers.setdefault(key,path);sizes[key]=len(data);return key
    contexts={}
    for label,repo,evidence in[("original",a.original_repository.resolve(),a.original_evidence.resolve()),("rebased",a.current_repository.resolve(),a.current_evidence.resolve())]:
        helpers=json.loads((evidence/"verified-helpers.json").read_text());version=json.loads((evidence/"serial/baseline-results.json").read_text())["version"];records={};fingerprints={}
        def visit(source):
            if source in records:return fingerprints[source]
            path=repo/source;text=path.read_text();deps=[]
            for line in mask(text).splitlines():
                if line.startswith("import "):
                    for token in line.split()[1:]:
                        dep=module_to_path(token).as_posix()
                        if(repo/dep).is_file():visit(dep);deps.append(dep)
            expected=h((version+text+"".join(fingerprints[d]for d in deps)).encode())
            target=evidence/"serial/olean"/Path(source).with_suffix(".olean");meta_path=target.with_suffix(".audit-result.json");meta=json.loads(meta_path.read_text());log=Path(meta["log"])
            assert meta["exit"]==0 and meta["resource_stop"]is None and meta["source_transitive_sha256"]==expected,source
            ob=blob(target);lb=blob(log);assert ob==meta["olean_sha256"]and lb==meta["log_sha256"]
            records[source]=dict(source_blob=blob(path),olean_blob=ob,log_blob=lb,metadata_blob=blob(meta_path),dependencies=deps);fingerprints[source]=expected;return expected
        for module in helpers["modules"]:visit(module["source"])
        reports={name:blob(evidence/name)for name in["verified-helpers.json","original-coverage-ledger.json","remaining-original-records.json","all-reviewed-pure-input-roles.json","acceptance-snapshot.json","mapped-module-dispositions.json","verified-payable.json","verified-totality.json"]}
        mapped=json.loads((evidence/"mapped-module-dispositions.json").read_text());mapped_sources={row["file"]:blob(repo/row["file"])for row in mapped["modules"]}
        contexts[label]={"repository_provenance":str(repo),"git_head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=repo,text=True).strip(),"lean_version":version,"modules":records,"reports":reports,"mapped_sources":mapped_sources}
    history=json.loads(a.history_record.read_text());assert contexts["original"]["git_head"]==history["frozen_commit"]and history["original_tracked_sources_unchanged"]is True
    attachments={"frozen-history-audit.json":blob(a.history_record),"original-typed-census.json":blob(a.historical_evidence/"verified-census.json")}
    for name in["original-frozen-assignment.txt","original-work-and-backfill-queue.md","scope-manifest.json","CURRENT-QUEUE-20261107.md","COORDINATOR-ANSWERS-20261107.json"]:
        attachments[name]=blob(a.current_repository/"scripts/h62/item2/audit-theories/handoff"/name)
    index={"schema_version":1,"contexts":contexts,"attachments":attachments,"blob_sizes":sizes,
      "boundary":"Portable source/import/artifact/log/hash and axiom-log checks only; no kernel rerun, original/current equivalence, operational static refusal or full assignment acceptance.","full_assignment_acceptance":False}
    output.parent.mkdir(parents=True,exist_ok=True)
    with output.open("wb")as raw,gzip.GzipFile(filename="",fileobj=raw,mode="wb",compresslevel=3,mtime=0)as gz,tarfile.open(fileobj=gz,mode="w|")as tar:
        def add(name,data):
            item=tarfile.TarInfo(name);item.size=len(data);item.mtime=0;tar.addfile(item,io.BytesIO(data))
        add("index.json",canonical(index))
        for key in sorted(providers):
            data=providers[key].read_bytes();assert h(data)==key;add("blobs/"+key,data)
    print(json.dumps({"archive":str(output),"sha256":h(output.read_bytes()),"blobs":len(providers),"contexts":{k:len(v["modules"])for k,v in contexts.items()}}))
def verify(a):
    source_data={};seen=set();index=None
    with tarfile.open(a.archive,mode="r|gz")as tar:
        for member in tar:
            assert member.isfile()and not member.issym()
            stream=tar.extractfile(member)
            if member.name=="index.json":
                assert index is None;index=json.loads(stream.read());needed=set(index["attachments"].values());referenced=set(needed)
                for context in index["contexts"].values():
                    referenced.update(context["reports"].values());referenced.update(context["mapped_sources"].values())
                    for row in context["modules"].values():referenced.update(row[k]for k in("source_blob","metadata_blob","log_blob","olean_blob"))
                assert referenced<=set(index["blob_sizes"]),"Referenced artifact missing from blob index"
                for ctx in index["contexts"].values():
                    needed.update(ctx["reports"].values());needed.update(ctx["mapped_sources"].values())
                    for row in ctx["modules"].values():needed.update(row[k]for k in("source_blob","metadata_blob","log_blob"))
                continue
            assert index is not None and member.name.startswith("blobs/")
            key=member.name[6:];assert key in index["blob_sizes"]and key not in seen;seen.add(key)
            digest=hashlib.sha256();parts=[];size=0
            while True:
                part=stream.read(1024*1024)
                if not part:break
                digest.update(part);size+=len(part)
                if key in needed:parts.append(part)
            assert size==index["blob_sizes"][key]and digest.hexdigest()==key,"Blob integrity failure"
            if key in needed:source_data[key]=b"".join(parts)
    assert index is not None and seen==set(index["blob_sizes"])and index["full_assignment_acceptance"]is False
    summaries={}
    typed_raw=source_data[index["attachments"]["original-typed-census.json"]];typed=json.loads(typed_raw);originals={r["source_name"]:r for r in typed["declarations"]}
    assert len(originals)==len(typed["declarations"])==500 and len(typed["generated_candidates"])==986
    decision_raw=source_data[index["attachments"]["COORDINATOR-ANSWERS-20261107.json"]];decisions=json.loads(decision_raw);decision_sha=h(decision_raw)
    assert decisions["answers"]["Q-FROZEN-REBASE"].startswith("option 1.")and decisions["answers"]["Q-STATIC-VALUE"].startswith("option 3.")
    static_name="Solidity.Theory.Mutability.ContractWorld.World.enter_static"
    scope=json.loads(source_data[index["attachments"]["scope-manifest.json"]]);frozen_sources={k:v for k,v in scope["source_inputs_sha256"].items()if k.endswith(".lean")};assert len(frozen_sources)==25
    H69_NAMES={"Solidity.Theory.Progress.Val.not_tuple","Solidity.Theory.Progress.Controls.no_tuple_local","Solidity.Ty.Finite.not_array",static_name}
    for label,ctx in index["contexts"].items():
        records=ctx["modules"];fps={}
        def fingerprint(source):
            if source in fps:return fps[source]
            row=records[source];text=source_data[row["source_blob"]].decode().replace("\r\n","\n").replace("\r","\n");deps=[]
            for line in mask(text).splitlines():
                if line.startswith("import "):
                    for token in line.split()[1:]:
                        dep=module_to_path(token).as_posix()
                        if dep in records:deps.append(dep)
            assert deps==row["dependencies"]
            expected=h((ctx["lean_version"]+text+"".join(fingerprint(d)for d in deps)).encode());meta=json.loads(source_data[row["metadata_blob"]])
            assert meta["exit"]==0 and meta["resource_stop"]is None and meta["source_transitive_sha256"]==expected
            assert meta["olean_sha256"]==row["olean_blob"]and meta["log_sha256"]==row["log_blob"]and meta["command"][-1]==source
            fps[source]=expected;return expected
        for source in records:fingerprint(source)
        reports={n:json.loads(source_data[key])for n,key in ctx["reports"].items()};helpers=reports["verified-helpers.json"];names=set()
        for module in helpers["modules"]:
            source=module["source"];row=records[source];log=source_data[row["log_blob"]].decode();assert "sorryAx"not in log and not re.search(r"\b(?:error(?:\([^)]*\))?|warning):",log)
            declared={d["source_name"]for d in scan(source_data[row["source_blob"]].decode(),source)};assert declared=={t["name"]for t in module["theorems"]}
            for theorem in module["theorems"]:
                name=theorem["name"];assert name not in names;names.add(name)
                match=re.search("'"+re.escape(name)+r"' (does not depend on any axioms|depends on axioms: \[([^]]*)\])",log);assert match
                axioms={s.strip()for s in(match[2]or"").split(",")if s.strip()};assert axioms<=ALLOW and sorted(axioms)==theorem["axioms"]
        assert len(names)==helpers["proved_theorems"]
        by_helper={item["name"]:(module,item)for module in helpers["modules"]for item in module["theorems"]}
        def check_certificate(cert):
            assert cert["theorem"]in by_helper
            module,item=by_helper[cert["theorem"]];meta=json.loads(source_data[records[module["source"]]["metadata_blob"]])
            assert cert["source"]==module["source"]and cert["axioms"]==item["axioms"]and cert["log"]==meta["log"]
        snap=reports["acceptance-snapshot.json"];pay=reports["verified-payable.json"];ledger=reports["original-coverage-ledger.json"];roles=reports["all-reviewed-pure-input-roles.json"];gaps=reports["remaining-original-records.json"]
        for report in(snap,pay,ledger,roles):assert report["full_assignment_acceptance"]is False
        assert h(typed_raw)==ledger["historical_typed_snapshot_sha256"]and typed["base"]==ledger["frozen_assignment_base"]
        entries=ledger["original_explicit_declarations"];assert len(entries)==len({r["source_name"]for r in entries})==500
        assert{r["source_name"]for r in entries}==set(originals);by_name={r["source_name"]:r for r in entries}
        counts=dict(Counter(r["status"]for r in entries));assert counts==ledger["original_explicit_counts"]
        joint={r["source_name"]for r in entries if r["status"]=="joint-certificate-present-version-fidelity-separate"}
        intentional={r["source_name"]for r in entries if r["status"]=="H69-intentional-impossibility-certificate-present"};assert intentional==H69_NAMES
        assert len(joint)==snap["joint_certificates"]and len(intentional)==snap["accepted_H69"],"Snapshot/ledger counts mismatch"
        assert snap["checked_helper_theorems"]==len(names)and snap["original_explicit_declarations"]==500 and snap["original_generated_pending"]==986
        assert snap["current_head"]==ctx["git_head"],"Snapshot/context commit mismatch"
        expected_gaps={}
        for row in entries:
            name=row["source_name"];orig=originals[name]
            for key in("file","line","visibility","source_header","elaborated_type_sha256","documented_producing_lane","proving_owner"):assert row[key]==orig[key]
            if name in joint or name in intentional:check_certificate(row["current_certificate"])
            elif row["status"]=="historical-empty-input-telescope":assert orig["status"]=="no-inputs"
            else:
                assert row["status"]==("private-witness-pending"if orig["visibility"]=="private"else"public-witness-pending")
                key=orig["elaborated"]["name"];expected_gaps[key]={"theorem":key,"source_name":name,"file":row["file"],"line":row["line"],"status":row["status"],"documented_producing_lane":row["documented_producing_lane"],"proving_owner":row["proving_owner"]}
        for row in typed["generated_candidates"]:
            expected_gaps[row["name"]]={"theorem":row["name"],"source_name":None,"file":row["file"],"line":None,"status":"original-generated-candidate-pending","documented_producing_lane":row["documented_producing_lane"],"proving_owner":row["proving_owner"]}
        assert len(gaps)==len({r["theorem"]for r in gaps})==len(expected_gaps)==ledger["remaining_original_records"]==snap["remaining_original_records"]
        assert{r["theorem"]for r in gaps}==set(expected_gaps)and all(r==expected_gaps[r["theorem"]]for r in gaps)
        policy=ledger["fidelity_disposition"];assert policy==snap["fidelity_disposition"]and policy["status"]=="resolved-history-based-original-audit"and policy["frozen_base"]==typed["base"]and policy["decision_sha256"]==decision_sha
        static=by_name[static_name]
        static_expected={"status":"H69-intentional-impossibility-certificate-present","accepted_H69":True,"scope_decision":"Q-STATIC-VALUE","decision_sha256":decision_sha,"operational_refusal_coverage":False}
        assert all(static[k]==value for k,value in static_expected.items()),"Static boundary metadata mismatch"
        assert static["intentional_reason"]=="Intentional H69 separation boundary: static calls with nonzero value are excluded on purpose because the EVM forbids them. Frozen Context.Mode makes the joint hypotheses impossible."
        role_names=[r["theorem"]for r in roles["declarations"]];assert len(role_names)==len(set(role_names))==roles["reviewed_role_records"]==roles["cumulative_original_roles"]==snap["reviewed_roles"]
        assert 500-len(role_names)==roles["remaining_original_roles"]==snap["remaining_roles"]
        role_joint=0;role_intentional=0
        for row in roles["declarations"]:
            name=row["theorem"];orig=originals[name]
            assert row["source_header"]==orig["source_header"]and row["historical_frozen_elaborated_type_sha256"]==orig["elaborated_type_sha256"]
            assert[{k:v for k,v in b.items()if k not in("role","index")}for b in row["binders"]]==orig["elaborated"]["binders"]
            if name==static_name:
                assert all(row[k]==value for k,value in static_expected.items())and row["intentional_reason"]==static["intentional_reason"],"Static role metadata mismatch"
                assert row["current_impossibility_certificate"]==static["current_certificate"]and"current_joint_certificate"not in row;role_intentional+=1
            else:
                assert name in joint and row.get("status","joint-witness-checked")=="joint-witness-checked"and not row.get("accepted_H69",False)
                assert row["current_joint_certificate"]==by_name[name]["current_certificate"];role_joint+=1
        assert role_joint==roles["joint_certificates_in_role_union"]and role_intentional==roles["accepted_H69_in_role_union"]and roles["ordinary_pending_impossibilities"]==0
        pay_rows=pay["declarations"];assert len(pay_rows)==len({r["source_name"]for r in pay_rows})==7
        pay_static=next(r for r in pay_rows if r["source_name"]==static_name)
        assert all(pay_static[k]==value for k,value in static_expected.items())and pay_static["intentional_reason"]==static["intentional_reason"]and pay_static["certificate"]==static["current_certificate"],"Static Payable row mismatch"
        assert pay["static_operational_refusal_coverage"]is False and pay["joint_witnesses"]==6 and pay["accepted_H69"]==1 and pay["pending_impossibilities"]==0 and pay["ordinary_joint_complete"]is True
        for row in pay_rows:
            name=row["source_name"];orig=originals[name]
            assert orig["file"]=="Solidity/Theory/Mutability/Payable.lean"and row["source_header"]==orig["source_header"]
            if name!=static_name:assert name in joint and row["status"]=="joint-witness-checked"and row["certificate"]==by_name[name]["current_certificate"]
        for cert in pay["positive_model_API_controls"]:check_certificate(cert)
        assert{c["theorem"]for c in pay["positive_model_API_controls"]}=={"H62.AuditTheories.payable_system_positive_control","H62.AuditTheories.payable_enter_positive_control","H62.AuditTheories.payable_call_positive_control"}
        mapped=reports["mapped-module-dispositions.json"];assert len(ctx["mapped_sources"])==mapped["original_mapped_files"]==len(mapped["modules"])==25
        assert set(ctx["mapped_sources"])=={r["file"]for r in mapped["modules"]}==set(frozen_sources)
        for row in mapped["modules"]:
            blob_key=ctx["mapped_sources"][row["file"]];assert blob_key==row["current_source_sha256"],"Mapped source integrity mismatch"
            if row["file"]in records:assert blob_key==records[row["file"]]["source_blob"],"Mapped/proof source mismatch"
            assert row["original_source_sha256"]==frozen_sources[row["file"]]and row["source_byte_unchanged"]==(blob_key==frozen_sources[row["file"]])
            module_rows=[r for r in entries if r["file"]==row["file"]];assert row["original_explicit_declarations"]==len(module_rows)and row["original_dispositions"]==dict(Counter(r["status"]for r in module_rows))
            if label=="original":assert row["source_byte_unchanged"]and blob_key==row["original_source_sha256"]
        summaries[label]={"git_head":ctx["git_head"],"helpers":len(names),"dependency_modules":len(records),"joint":snap["joint_certificates"],"H69":snap["accepted_H69"],"pending":snap["remaining_original_records"]}
    history=json.loads(source_data[index["attachments"]["frozen-history-audit.json"]]);assert summaries["original"]["git_head"]==history["frozen_commit"]==typed["base"]==scope["base"],"Original history identity mismatch"
    original=index["contexts"]["original"];current=index["contexts"]["rebased"]
    helper_sources=[m["source"]for m in json.loads(source_data[original["reports"]["verified-helpers.json"]])["modules"]]
    assert all(original["modules"][s]["source_blob"]==current["modules"][s]["source_blob"]for s in helper_sources),"Helper overlays differ"
    print("PAIRED_PORTABLE_EVIDENCE_PASS "+json.dumps({"contexts":summaries,"blobs":len(seen),"identical_helper_modules":len(helper_sources),"old_VM_paths_opened":0,"kernel_rerun":False,"full_assignment_acceptance":False}))
def main():
    ap=argparse.ArgumentParser(description=__doc__);sub=ap.add_subparsers(dest="mode",required=True);ex=sub.add_parser("export")
    for n in("current-repository","current-evidence","original-repository","original-evidence","history-record","historical-evidence","out"):ex.add_argument("--"+n,type=Path,required=True)
    ve=sub.add_parser("verify");ve.add_argument("--archive",type=Path,required=True);a=ap.parse_args();export(a)if a.mode=="export"else verify(a)
if __name__=="__main__":main()
