#!/usr/bin/env python3
"""H70 structural classification, not semantic equivalence or API acceptance.
Usage: classify_api.py OLD_RESULT NEW_RESULT [OUTPUT_DIRECTORY]
Preserves all 64 source deltas and all generated/private declarations.
"""
import collections,hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
EVIDENCE=Path("/workspace/migrate-roadmap-evidence")
def digest(path):
    with path.open("rb") as f:return hashlib.file_digest(f,"sha256").hexdigest()
def write(path,value):path.write_text(json.dumps(value,indent=2,sort_keys=True)+"\n")
def unsupported(value):
    if isinstance(value,list):
        if value and isinstance(value[0],str) and value[0].startswith("unsupported-"):return True
        return any(unsupported(x) for x in value)
    return False
def classify(old,new):
    if unsupported(old["alpha"]) or unsupported(new["alpha"]):raise ValueError("unsupported structural input")
    if old["universe_count"]!=new["universe_count"]:return "structural"
    if old["alpha"]==new["alpha"]:return "alpha_only"
    if old["binder_erased"]==new["binder_erased"]:return "binder_visibility_only"
    return "structural"
def first_difference(old,new,path=()):
    if old==new:return None
    if isinstance(old,list) and isinstance(new,list) and len(old)==len(new):
        for i,(a,b) in enumerate(zip(old,new)):
            difference=first_difference(a,b,path+(i,))
            if difference is not None:return difference
    return dict(path=list(path),old=old,new=new)
def family(name):
    if "noConfusion" in name:return "generated_noConfusion"
    if "sizeOf" in name:return "generated_sizeOf"
    if "instDecidableEq" in name:return "derived_decidable_equality"
    if "instRepr" in name:return "derived_representation"
    if "beBytes._proof_" in name:return "generated_termination_proof"
    return "unclassified_family"
def load(path):
    path=Path(path).resolve();assert path.is_relative_to(EVIDENCE)
    run=json.loads(path.read_text());assert run["exit"]==0 and run["guard"] is None
    assert run["inputs_before"]==run["inputs_after"]
    assert digest(Path(run["command"][-1]))==run["script_sha256"]
    rows=[];controls=0
    for line in path.with_name("build.log").read_text().splitlines():
        if "CANONICAL_API {" in line:rows.append(json.loads(line.split("CANONICAL_API ",1)[1]))
        if "CANONICAL_CONTROLS_PASS 4" in line:controls+=1
    assert controls==1 and len({r["name"] for r in rows})==len(rows)
    assert all(not unsupported(r["alpha"]) for r in rows)
    return run,{r["name"]:r for r in rows}
def logged_compile_times(result_path):
    times={}
    for line in Path(result_path).with_name("build.log").read_text().splitlines():
        match=re.search(r"Built (Solidity[.][A-Za-z0-9_.]+) \(([0-9.]+)(ms|s)\)",line)
        if match:times[match[1]]=dict(reported=match[2]+match[3],seconds=float(match[2])/(1000 if match[3]=="ms" else 1))
    return times
def main():
    if len(sys.argv) not in (3,4):raise SystemExit(__doc__)
    old_path,new_path=sys.argv[1:3]
    out=Path(sys.argv[3]) if len(sys.argv)==4 else EVIDENCE/"h70"/"classification"
    assert out.resolve().is_relative_to(EVIDENCE/"h70");out.mkdir(parents=True,exist_ok=True)
    old,a=load(old_path);new,b=load(new_path)
    assert old["resources"]==new["resources"] and old["tooling_sha256"]==new["tooling_sha256"]
    common=old["inputs_after"].keys() & new["inputs_after"].keys()
    assert all(old["inputs_after"][k]==new["inputs_after"][k] for k in common)
    assert all(digest(ROOT/k)==v for run in (old,new) for k,v in run["inputs_after"].items())
    delta=json.loads((EVIDENCE/"api-compatibility-deltas.json").read_text())
    assert len(a)==392 and len(b)==391
    assert sorted(a.keys()-b.keys())==sorted(r["name"] for r in delta["removed"])
    assert sorted(b.keys()-a.keys())==sorted(r["name"] for r in delta["added"])
    expected={r["name"]:r for r in delta["shared_debug_type_changes"]}
    changed={n for n in a.keys() & b.keys() if a[n]["type_debug"]!=b[n]["type_debug"]}
    assert changed==expected.keys() and len(changed)==64
    rows=[]
    for name in sorted(changed):
        prior=expected[name]
        assert a[name]["type_debug"]==prior["old"] and b[name]["type_debug"]==prior["new"]
        category=classify(a[name],b[name])
        rows.append(dict(name=name,family=family(name),category=category,
            old_type_debug=prior["old"],new_type_debug=prior["new"],
            first_alpha_difference=first_difference(a[name]["alpha"],b[name]["alpha"]),
            first_binder_erased_difference=first_difference(a[name]["binder_erased"],b[name]["binder_erased"]),
            compatibility="Root review retained; this classification grants no API exception"))
    counts=dict(collections.Counter(r["category"] for r in rows))
    assert counts==dict(alpha_only=45,binder_visibility_only=9,structural=10)
    write(out/"classification.json",dict(counts=counts,rows=rows,removed=delta["removed"],added=delta["added"],
        input_result_paths=[str(Path(old_path).resolve()),str(Path(new_path).resolve())],
        input_sha256={str(p):digest(p) for p in (Path(old_path),Path(new_path),ROOT/"tests/h62/item6/migrate-roadmap/CanonicalEvm.lean",EVIDENCE/"api-compatibility-deltas.json")},
        rules=dict(alpha_only="Identical structural types after binder-name and ordered universe-parameter-label normalization; binder visibility retained.",
                   binder_visibility_only="Difference disappears only after additionally erasing explicit/implicit/strict/instance binder info; API-visible change remains.",
                   structural="Difference remains after those normalizations, or declaration universe arity changes; requires a preserving root strategy."),
        boundary="Syntactic inspection of elaborated closed Expr trees. No defeq normalization, constant unfolding, reordering, API exemption, kernel equivalence proof or semantic acceptance."))
    percent=100*(new["wall_seconds"]/old["wall_seconds"]-1)
    rss_percent=100*(new["sampled_peak_aggregate_rss_bytes"]/old["sampled_peak_aggregate_rss_bytes"]-1)
    write(out/"timing-escalation.json",dict(id="B-PERF-INSPECTION",old_wall_seconds=old["wall_seconds"],new_wall_seconds=new["wall_seconds"],delta_percent=percent,
        old_sampled_peak_aggregate_rss_bytes=old["sampled_peak_aggregate_rss_bytes"],new_sampled_peak_aggregate_rss_bytes=new["sampled_peak_aggregate_rss_bytes"],rss_delta_percent=rss_percent,
        stopped_further_lean=percent>10 or rss_percent>10,kind="Supplemental inspection workload, not a full assigned-directory build benchmark",
        model_compile_log_observations=dict(old=logged_compile_times(old_path),new=logged_compile_times(new_path)),
        limitation="Logged module times have limited precision. Inspection includes helper compilation and metadata serialization; it does not establish directory-wide checking slowdown.",
        request="Root gate investigates this >10% supplemental-probe increase before further worker Lean runs. Full matched migration timing acceptance remains pending."))
    print(json.dumps(dict(classified=len(rows),counts=counts,probe_delta_percent=percent,probe_rss_delta_percent=rss_percent,stop_further_lean=percent>10 or rss_percent>10)))
if __name__=="__main__":main()
