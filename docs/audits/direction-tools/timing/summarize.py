#!/usr/bin/env python3
"""Small audit findings, not raw receipts. Run from repository root:
python3 docs/audits/direction-tools/timing/summarize.py --out DIR [--sample EXTERNAL/sample-results.json]
Partial coverage never becomes a complete build estimate or matched verdict.
"""
import argparse,collections,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--out',type=pathlib.Path,required=True); ap.add_argument('--sample',type=pathlib.Path); args=ap.parse_args()
    inv=json.loads((HERE/'inventory.json').read_text()); sample=json.loads(args.sample.read_text()) if args.sample else {'samples':[]}
    assert sample.get('base',inv['base'])==inv['base']
    passed=[r for r in sample['samples'] if r.get('status')=='pass']; byarea=collections.defaultdict(list)
    for row in passed: byarea[row['area']].append(row)
    perarea=[]
    for area in inv['largest_areas']:
        rows=byarea[area]; count=len(rows); lines=sum(r['lines'] for r in rows); seconds=sum(r['plain']['wall_seconds'] for r in rows)
        perarea.append({'area':area,**inv['areas'][area],'passing_samples':count,'sample_lines':lines,'sample_wall_seconds':seconds,'sample_seconds_per_kloc':1000*seconds/lines if lines else None,'reference_ratios':None,'verdict':'pending matched reference checks'})
    summary={'status':'partial','base':inv['base'],'checkpoints':{'inventory':'done','local_stratified_measurement':'partial','declaration_ranking':'partial','reference_builds':'pending','full_build_estimate':'pending','incremental_graph':'done','ten_prioritized_changes':'pending','final_reviews':'pending','clean_checkout_reproduction':'pending','handoff':'pending'},'tracked_lean_modules':sum(a['modules'] for a in inv['areas'].values()),'tracked_lean_lines':sum(a['lines'] for a in inv['areas'].values()),'areas':perarea,'incremental':inv['incremental'],'build_workloads':inv['build_workloads'],'historical':{'observations':len(inv['historical']['samples']),'source':inv['historical']['source'],'source_base':inv['historical']['source_base'],'use':'inventory only; not pooled with fresh timings'},'fresh_passing_samples':len(passed),'fresh_attempted_samples':len(sample['samples']),'sample_plan_modules':len(inv['sample_plan']),'sample_method':'four deterministic physical-size quantile midpoint modules per largest area; targeted slow/generated strata still pending; no statistical representativeness asserted','slowest_sampled_modules':sorted([{'path':r['path'],'lines':r['lines'],'wall_seconds':r['plain']['wall_seconds']} for r in passed],key=lambda r:-r['wall_seconds'])[:20],'slowest_sampled_declarations':None,'full_build_estimate_seconds':None,'published_reference_times':json.loads((HERE/'published-times.json').read_text()),'limitations':['no systemd scope on the cloud VM (H232); 12 GiB conservative process-group RSS stop, 3 GiB available-memory reserve; no swap','Toolchain is Lean 4.24.0 / Lake 5.0.0-src+797c613; reference pins use different versions','First mixed-artifact-cache attempt discarded; only clean detached-worktree observations retained','Basic profiler threshold suppressed to avoid guard_msgs contamination; structured traces provide command attribution at 100 ms threshold','All-tracked reverse closure is potential invalidation; named workload closures model requested build targets, not measured rebuild execution','Generated paths and bounded spans separated from ambiguous markers and unmarked source; unmarked does not mean handwritten','No matched ratios or full-build estimates until required sampling and reference checks finish'],'waits':[{'id':'compcert-published-time','reason':'manual host returned proxy 403; pinned source README contains no numeric proof-build time','next':'seek a public cited mirror or paper; continue other items'},{'id':'clear-toolchain','reason':'official v4.9.1 Linux release archive returned 404; tag exists','next':'inspect official release metadata or source-supported installation route; do not substitute toolchain'}]}
    args.out.mkdir(parents=True,exist_ok=True); (args.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'status':summary['status'],'modules':summary['tracked_lean_modules'],'lines':summary['tracked_lean_lines'],'passing':len(passed)}))
if __name__=='__main__': main()
