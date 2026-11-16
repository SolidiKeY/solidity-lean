#!/usr/bin/env python3
"""Reuse integrated audit results at an immutable commit; no new measurements.
Run: python3 -I docs/audits/direction-tools/statements/reuse.py [--check]
The census covers Solidity modules; this lane inventories all tracked Lean.
Other lanes completion permissions and component pairs do not establish new
statement counterparts or historical authorship for this lane.
"""
import argparse,collections,csv,hashlib,json,pathlib,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/"scan.py"),run_name="statement_reuse_api")
INPUT_REV="cf3baafd2202adf0107c5ae4d2879cd04ff0aec5"

def generate():
    inputs={}
    def read(path):
        raw=subprocess.check_output(["git","show",INPUT_REV+":"+path],cwd=API["ROOT"])
        inputs[path]=hashlib.sha256(raw).hexdigest()
        return json.loads(raw)
    prefix="docs/audits/direction-tools/"
    census=read(prefix+"census/census.json")
    assert census["revision"]==API["BASE"]
    modules={m["path"]:m for name in census["module_chunks"] for m in read(prefix+"census/"+name)}
    own_provenance=json.loads((HERE/"provenance.json").read_text())
    unknown=[r for r in own_provenance["records"] if r["category"]=="unresolved_chain_agreement"]
    covered=[modules[r["path"]] for r in unknown if r["path"] in modules]
    outside=[r["path"] for r in unknown if r["path"] not in modules]
    assert all(not p.startswith("Solidity/") for p in outside),"Census unexpectedly omits a Solidity module"
    selected=sorted({r["path"] for r in csv.DictReader((HERE/"statements.csv").open())})
    selected_modules=[]
    for path in selected:
        module=modules[path]
        source=API["frozen_text"](path)
        declarations=API["declarations"](path,source,API["mask"](source))
        assert module["lines"]==len(source.splitlines()),path
        assert module["declarations"].get("theorem",0)==sum(d["kind"]=="theorem" for d in declarations),path
        selected_modules.append({k:module[k] for k in ("path","category","lines","generated_lines","imports_in","declarations")})
    pins=read(prefix+"references/pins.json")
    own_refs=json.loads((HERE/"references.json").read_text())
    pin_comparison=[]
    for ref in own_refs:
        name={"compcert":"CompCert","cakeml":"CakeML"}[ref["id"]]
        own_pin=ref["url"].split("/")[5]
        pin_comparison.append(dict(reference=name,statement_pin=own_pin,merged_reference_pin=pins[name],same_revision=own_pin==pins[name]))
    own_solc=json.loads((HERE/"calibration.json").read_text())["solc_snapshot"]["commit"]
    pin_comparison.append(dict(reference="solc",statement_pin=own_solc,merged_reference_pin=pins["solc"],same_revision=own_solc==pins["solc"]))
    specs=read(prefix+"references/pair-specs.json")
    matching=[r for r in specs if set(r["this_paths"])&set(selected)]
    boundaries=read(prefix+"references/boundaries.json")
    process=read(prefix+"process/generated-paths.json")
    exceptions=[]
    for path in ("Solidity/Corpus/Basic.lean","Solidity/Corpus/Imported.lean"):
        own=next(r for r in own_provenance["records"] if r["path"]==path)
        exceptions.append(dict(path=path,statement_category=own["category"],process_category=process.get(path),resolution="Retain the explicit handwritten exception documented by pinned scripts/check-corpus.sh; do not overwrite with a broader directory classification."))
    return dict(base=API["BASE"],completion_authorization=API["COMPLETION_AUTHORIZATION"],integrated_inputs_commit=INPUT_REV,input_sha256=dict(sorted(inputs.items())),method="Reuse committed census/reference/process artifacts. Counts remain lexical; no new corpus, reference checkout, proof or timing run.",selected_module_census=selected_modules,untraced_reconciliation=dict(total=len(unknown),within_census=len(covered),census_categories=dict(sorted(collections.Counter(m["category"] for m in covered).items())),census_marked_generated_lines=sum(m["generated_lines"] for m in covered),outside_census_count=len(outside),outside_census_paths=outside,boundary="Census unmarked/import-only status supplies no historical origin certificate. Outside-census files are outside Solidity/, not omitted Solidity modules."),reference_reconciliation=dict(pins=pin_comparison,direct_selected_module_pairs=len(matching),pairs=matching,missing_counterparts=boundaries["missing_counterparts"],boundary="File-level pairs are not theorem-level analogues. Different CakeML/solc revisions must not be pooled with statement-specific measurements. The other reference lanes H242 completion permission is not adopted as a scope waiver here."),handwritten_exception_reconciliation=exceptions,conclusion="Integrated artifacts corroborate selected-module counts but supply no further direct selected-module pair or historical producer records. H243 authorizes explicit null ratios for unmatched units; H244 accepts separately reported generated, handwritten and untraced categories. Neither implies additional measurement or a historical origin certificate.")

def main():
    p=argparse.ArgumentParser();p.add_argument("--check",action="store_true");a=p.parse_args();data=generate()
    body=json.dumps(data,ensure_ascii=False,indent=2)+"\n";target=HERE/"reuse.json"
    if a.check:assert target.read_text()==body,"STALE reuse.json"
    else:target.write_text(body)
    print("REUSE_PASS",len(data["selected_module_census"]),"selected modules;",data["untraced_reconciliation"]["within_census"],"untraced paths covered;",data["reference_reconciliation"]["direct_selected_module_pairs"],"new direct pairs")
if __name__=="__main__":main()
