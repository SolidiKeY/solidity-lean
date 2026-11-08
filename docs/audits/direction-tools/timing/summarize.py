#!/usr/bin/env python3
"""Small audit findings, not raw receipts. Run from repository root:
python3 docs/audits/direction-tools/timing/summarize.py --out DIR [--sample EXTERNAL/sample-results.json]
Partial coverage never becomes a complete build estimate or matched verdict.
"""
import argparse,collections,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--out',type=pathlib.Path,required=True); ap.add_argument('--sample',type=pathlib.Path); ap.add_argument('--analysis',type=pathlib.Path,help='validated analyze.py output, optional'); args=ap.parse_args()
    inv=json.loads((HERE/'inventory.json').read_text()); sample=json.loads(args.sample.read_text()) if args.sample else {'samples':[]}
    assert sample.get('base',inv['base'])==inv['base']
    passed=[r for r in sample['samples'] if r.get('status')=='pass']; byarea=collections.defaultdict(list)
    for row in passed: byarea[row['area']].append(row)
    perarea=[]
    for area in inv['largest_areas']:
        rows=byarea[area]; stratified=[r for r in rows if r.get('selection')=='size_quartile_midpoint']; strat_lines=sum(r['lines'] for r in stratified); strat_seconds=sum(r['plain']['wall_seconds'] for r in stratified); count=len(rows); lines=sum(r['lines'] for r in rows); seconds=sum(r['plain']['wall_seconds'] for r in rows)
        perarea.append({'area':area,**inv['areas'][area],'passing_samples':count,'size_stratified_passing_samples':len(stratified),'size_stratified_seconds_per_kloc':1000*strat_seconds/strat_lines if strat_lines else None,'targeted_passing_samples':count-len(stratified),'sample_lines':lines,'sample_wall_seconds':seconds,'sample_seconds_per_kloc':1000*seconds/lines if lines else None,'reference_ratios':None,'verdict':'pending matched reference checks'})
    summary={'status':'partial','base':inv['base'],'checkpoints':{'inventory':'done','local_stratified_measurement':'partial','declaration_ranking':'partial','reference_builds':'pending','full_build_estimate':'pending','incremental_graph':'done','ten_prioritized_changes':'pending','final_reviews':'pending','clean_checkout_reproduction':'pending','handoff':'pending'},'tracked_lean_modules':sum(a['modules'] for a in inv['areas'].values()),'tracked_lean_lines':sum(a['lines'] for a in inv['areas'].values()),'measurement_versions':sample.get('versions'),'measurement_environment':sample.get('environment'),'areas':perarea,'incremental':inv['incremental'],'build_workloads':inv['build_workloads'],'historical':{'observations':len(inv['historical']['samples']),'source':inv['historical']['source'],'source_base':inv['historical']['source_base'],'use':'inventory only; not pooled with fresh timings'},'samples_missing_environment_metadata':sum(r.get('observation_environment') is None for r in passed),'fresh_passing_samples':len(passed),'fresh_attempted_samples':len(sample['samples']),'sample_plan_modules':len(inv['sample_plan']),'sample_method':'four deterministic physical-size quantile midpoint modules per largest area plus targeted slow/generated files; size-stratified rates reported separately; no statistical representativeness asserted','slowest_sampled_modules':sorted([{'path':r['path'],'lines':r['lines'],'wall_seconds':r['plain']['wall_seconds']} for r in passed],key=lambda r:-r['wall_seconds'])[:20],'slowest_sampled_declarations':None,'full_build_estimate_seconds':None,'published_reference_times':json.loads((HERE/'published-times.json').read_text()),'limitations':['Environment conditions are reported only when present in the supplied measurement metadata','Reference pins use different Lean versions; consult recorded measurement versions','The summary does not infer measurement provenance or discarded-run history from timing values','Structured profile thresholds and instrumentation must be read from individual recorded profile commands','All-tracked reverse closure is potential invalidation; named workload closures model requested build targets, not measured rebuild execution','Generated paths and bounded spans separated from ambiguous markers and unmarked source; unmarked does not mean handwritten','No matched ratios or full-build estimates until required sampling and reference checks finish'],'waits':[{'lane':'da-timing','item':r['path']+': '+r['status']} for r in sample['samples'] if r.get('status')!='pass']+[{'lane':'da-timing','item':r['project']+': '+r['error']} for r in json.loads((HERE/'published-times.json').read_text()) if r.get('status')=='unavailable']}
    if args.analysis:
        analysis=json.loads(args.analysis.read_text()); assert analysis['base']==inv['base']
        summary['calibration']=analysis
        summary['slowest_sampled_modules']=analysis['slowest_sampled_modules']
        summary['slowest_sampled_declarations']=(analysis.get('declaration_profiles') or {}).get('slowest_sampled_declarations')
        summary['full_build_estimate_seconds']=analysis['full_check_only_estimates']
        summary['baseline_only_counts']={'passing':summary['fresh_passing_samples'],'attempted':summary['fresh_attempted_samples'],'areas':summary['areas']}
        summary['fresh_passing_samples']=analysis['passing_current_modules']
        summary['fresh_attempted_samples']=analysis['attempted_observations']
        summary['areas']=analysis['per_area']
        summary['checkpoints'].update({'declaration_ranking':'partial','full_build_estimate':'partial','ten_prioritized_changes':'partial'})
        summary['limitations']=[s for s in summary['limitations'] if not s.startswith('No matched ratios or full-build estimates')]+analysis['limitations']
    args.out.mkdir(parents=True,exist_ok=True); (args.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'status':summary['status'],'modules':summary['tracked_lean_modules'],'lines':summary['tracked_lean_lines'],'passing':len(passed)}))
if __name__=='__main__': main()
