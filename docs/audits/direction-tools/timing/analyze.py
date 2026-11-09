#!/usr/bin/env python3
"""Derived check-only calibration; stdlib only. Never converts failed work to time0.
Run: analyze.py --inventory FILE --sample FILE [--extra FILE] [--reference FILE]
                --profiles FILE --repo REPO --out DIR
Model estimates are deterministic sample extrapolations, not measured full builds.
"""
import argparse,collections,json,pathlib,statistics,subprocess

def read(p): return json.loads(p.read_text())
def rate(rows):
    n=sum(r['lines'] for r in rows); t=sum(r['plain']['wall_seconds'] for r in rows)
    return {'modules':len(rows),'lines':n,'wall_seconds':t if rows else None,'seconds_per_kloc':1000*t/n if n else None}
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--inventory',type=pathlib.Path,required=True); ap.add_argument('--sample',type=pathlib.Path,required=True); ap.add_argument('--extra',type=pathlib.Path,action='append',default=[]); ap.add_argument('--reference',type=pathlib.Path,action='append',default=[]); ap.add_argument('--profiles',type=pathlib.Path); ap.add_argument('--verdicts',type=pathlib.Path); ap.add_argument('--repo',type=pathlib.Path,required=True); ap.add_argument('--out',type=pathlib.Path,required=True); args=ap.parse_args()
    inv=read(args.inventory); sample=read(args.sample); assert inv['base']==sample['base']; attempts=list(sample['samples']); decisions=read(args.verdicts) if args.verdicts else {}
    expected_cwds={r['area']:r.get('plain',r.get('cache',{})).get('cwd') for r in sample['samples']}
    def compatible(data):
        assert data['versions']==sample['versions'], 'local dataset toolchain mismatch'
        for row in data['samples']:
            if 'plain' not in row: continue
            cmd=row['plain']['command']
            expected=['lake','env','lean','-j1','--tstack=131072',row['path'].removeprefix('Bridge/') if row['path'].startswith('Bridge/') else row['path']]
            assert cmd==expected, 'local command protocol mismatch'
            assert row['plain']['cwd']==expected_cwds.get(row['area'],row['plain']['cwd']), 'measurement checkout mismatch'
    compatible(sample)
    for p in args.extra:
        extra=read(p); assert extra['base']==inv['base']; compatible(extra); attempts+=extra['samples']
    current={r['path']:r for r in attempts}; passing=[r for r in current.values() if r['status']=='pass']; strat=[r for r in passing if r.get('selection')=='size_quartile_midpoint']
    references={}
    for p in args.reference:
        ref=read(p); modules=ref['modules']
        pins={'EvmYul':'047f63070309f436b66c61e276ab3b6d1169265a','Clear':'6ef2e7eda01080e5d5fd7474354c1a71adab5071'}
        assert ref['pin']==pins[ref['project']] and ref.get('lean_version') and ref.get('lake_version'), 'reference provenance missing/mismatched'
        assert len({r['module'] for r in modules})==len(modules), 'duplicate reference modules'
        for row in modules:
            cmd=row['check']['command']
            assert cmd==['lake','env','lean','-j1','--tstack=131072','-DautoImplicit=false',row['path']], 'reference command protocol mismatch'
            assert row['check']['cwd']==ref['source'], 'reference checkout mismatch'
        complete=ref.get('status')=='pass' and len(modules)==ref.get('built_closure_modules') and all(r['check']['exit_code']==0 for r in modules)
        rows=[{'lines':r['lines'],'plain':r['check']} for r in modules if r['check']['exit_code']==0]
        references[ref['project']]={'pin':ref['pin'],'status':'pass' if complete else 'incomplete','expected_modules':ref.get('built_closure_modules'),'observed_modules':len(modules),'passing_modules':len(rows),'failed_module_observations':len(modules)-len(rows),'tracked_lean_lines':ref.get('tracked_lean_lines'),'built_closure_lines':ref.get('built_closure_lines'),'matched_check':rate(rows) if complete else None,'versions':{'lean':ref.get('lean_version'),'lake':ref.get('lake_version')},'preparation_build_attempts':[{'exit_code':r['exit_code'],'wall_seconds':r['wall_seconds'],'stop_reason':r.get('stop_reason'),'evidence_log':r['log']} for r in ref['build_attempts']],'dependency_cache_status':ref.get('cache',{}).get('exit_code'),'source_classes':{kind:rate([{'lines':r['lines'],'plain':r['check']} for r in modules if r['classification']==kind and r['check']['exit_code']==0]) for kind in ['detected_generated','unmarked_not_proven_handwritten']} if complete else None,'boundary':ref.get('measurement_boundary')}
    comparisons=[]
    for area in inv['largest_areas']:
        rows=[r for r in strat if r['area']==area]; local=rate(rows); expected={r['path'] for r in inv['sample_plan'] if r['area']==area and r.get('selection')=='size_quartile_midpoint'}; complete_local=expected=={r['path'] for r in rows} and len(expected)==4 and {r['quartile'] for r in rows}=={1,2,3,4}; refname='Clear' if area in ['Calculus','Examples','Bridge'] else 'EvmYul'; ref=references.get(refname); rr=ref.get('matched_check') if ref else None
        ratio=local['seconds_per_kloc']/rr['seconds_per_kloc'] if complete_local and local['seconds_per_kloc'] is not None and rr and rr['seconds_per_kloc'] else None
        outlier=None if ratio is None else (ratio>3 or ratio<1/3)
        decision=decisions.get(area) if outlier else None
        if decision:
            assert decision['verdict'] in ['justified','redundant','wrong-direction'] and decision.get('evidence')
            assert abs(decision['ratio']-ratio)<1e-9, 'stale outlier verdict'
        verdict=decision['verdict'] if decision else ('inconclusive' if ratio is None or outlier else 'within band; this looks fine')
        settling=None
        if ratio is None: settling='Complete the four planned local quartile checks and the pinned reference per-file protocol.'
        elif outlier and not decision: settling='One matched CPU/allocation profile experiment for the dominating local module and corresponding reference checks, accounting for wall time not attributed by Lean basic/structured profilers under unchanged budgets. This settles sampled hotspot attribution only; an area-wide verdict needs a closure census or independently representative wider sample.'
        comparisons.append({'area':area,'verdict_scope':'observed size-quartile sample only; area-wide representativeness is unestablished','local_quartile_coverage':{'expected':len(expected),'passed':len(rows),'complete':complete_local},'local_stratified':local,'local_all_samples':rate([r for r in passing if r['area']==area]),'local_source_classes':{kind:rate([r for r in passing if r['area']==area and r['classification']==kind]) for kind in sorted({r['classification'] for r in current.values() if r['area']==area}|{'detected_generated','unmarked_not_proven_handwritten'})},'source_inventory':inv['areas'][area],'reference':refname,'ratio':ratio,'outlier':outlier,'verdict':verdict,'reason':decision['reason'] if decision else ('No complete paired measurement.' if ratio is None else ('Observed threefold outlier; causal judgement requires the named component measurement.' if outlier else 'Observed check-time density is within the threefold band.')),'verdict_evidence':decision.get('evidence') if decision else None,'settling_measurement':settling,'comparability':'local toolchain, plain invocation flags and recorded checkout paths validated; per-observation machine identity is incomplete; source obligations and reference Lean versions differ; check-cost calibration, not proof productivity'})
    perarea=collections.defaultdict(list)
    for r in strat: perarea[r['area']].append(r['plain']['wall_seconds'])
    pooled_t=sum(r['plain']['wall_seconds'] for r in strat); pooled_l=sum(r['lines'] for r in strat); pooled_rate=pooled_t/pooled_l if pooled_l else None
    estimates={}
    for workload,info in inv['build_workloads'].items():
        if pooled_rate is None:
            estimates[workload]={'roots':info['roots'],'modules':info['reachable_modules'],'module_mean_model_seconds':None,'verdict':'inconclusive','settling_measurement':'Complete the planned size-stratified measurements before extrapolation.'}
            continue
        point=0; bylines=0; sensitivity_low=0; sensitivity_high=0; unsupported=[]
        for area,population in info['area_counts'].items():
            rows=[r for r in strat if r['area']==area]; times=perarea[area]
            if times:
                point+=population['modules']*statistics.mean(times)
                local_rate=sum(times)/sum(r['lines'] for r in rows); bylines+=population['lines']*local_rate
                sensitivity_low+=population['modules']*min(times); sensitivity_high+=population['modules']*max(times)
            else:
                unsupported.append(area); fallback=population['lines']*pooled_rate; point+=fallback; bylines+=fallback
                sensitivity_low+=fallback; sensitivity_high+=fallback
        estimates[workload]={'roots':info['roots'],'modules':info['reachable_modules'],'module_mean_model_seconds':point,'line_rate_sensitivity_model_seconds':bylines,'observed_extrema_sensitivity_seconds':[sensitivity_low,sensitivity_high],'pooled_extrapolation_areas':unsupported,'method':'area size-stratified mean observed per-module seconds times workload module count; unsampled areas use pooled seconds/line; targeted tails excluded; extrema are sensitivity scenarios, not statistical confidence bounds','boundary':'check-only body elaboration with warm imported oleans; excludes output/C generation, scheduling, downloads and dependency preparation; not an observed cold Lake build','verdict':'inconclusive','settling_measurement':'Serial CI per-module fresh-elaboration timings at the frozen base for these exact roots, summed with output generation measured separately.'}
    for model in estimates.values():
        point=model.get('module_mean_model_seconds')
        model['reference_total_check_ratios']={name:(point/ref['matched_check']['wall_seconds'] if point is not None and ref.get('matched_check') and ref['matched_check']['wall_seconds'] else None) for name,ref in references.items()}
        model['ratio_boundary']='Modelled complete local workload versus measured complete reference project body checks, warm imports. Different project sizes and Lean versions; no CompCert/CakeML ratio because their cited build boundaries differ.'
    advice={
      'Solidity/Examples/DecisionGaps.lean':'Run finite verdict assertions in a compiled mandatory test runner, retaining every expected outcome and all kernel theorem checks.',
      'Solidity/Examples/Tactics/RevertData.lean':'Reuse common checked byte-list and revert witnesses across the existing cases.',
      'Solidity/Yul/RawIntegerInitialization.lean':'Profile unattributed CPU/allocation cost first; if conversion normalization dominates, reuse checked range/conversion lemmas.',
      'Solidity/Examples/Tactics/QuantifiedDiamond.lean':'Share checked fuelled-execution lemmas across the loop and contract cases, preserving every case and fuel claim.',
      'Solidity/Calculus/ArrayProperty.lean':'Factor common array-transport equalities into reusable opaque checked intermediate lemmas.',
      'Solidity/Examples/DecisionHashThreeKinds.lean':'Reuse checked hash-coverage lemmas in place of repeated finite kernel reduction, preserving all hash-kind cases.',
      'Solidity/Calculus/Closer/Facts.lean':'Share checked operator-family strictness and eval-none lemmas instead of repeating constructor-case normalization.',
      'Solidity/Examples/Tactics/OwnStructs.lean':'Share typed contract metadata and checked struct witnesses while retaining every example proof.',
      'Solidity/Frontend/ExpressionUniqueness/AxiomPins.lean':'Memoize exact axiom-set traversals, preserving every exact/subset/non-growth pin.'}
    specs=[('Mathlib/Bridge cache','Make pinned proof-artifact delivery reliable through an available cache endpoint; retain source/toolchain hashes and checksum verification.',None),('Core invalidation fan-out','Keep frequently edited leaf proofs and tests separate from stable high-fan-out core APIs, preserving intrinsic types and every theorem obligation.',None)]
    hottest=sorted(passing,key=lambda row:(-row['plain']['wall_seconds'],row['path']))[:8]
    for row in hottest:
        path=row['path']; specs.append((path.removesuffix('.lean'),advice.get(path,'Use the clean component profile to factor reusable checked intermediate facts at the measured hotspot, retaining every theorem, premise and proof budget.'),path))
    changes=[]
    for name,change,path in specs:
        row=current.get(path) if path else None
        pool=row['plain']['wall_seconds'] if row and row['status']=='pass' else None
        basis={'kind':'observed module body check','path':path,'log':row['plain']['log']} if pool is not None else None
        if name=='Mathlib/Bridge cache':
            prep_costs=[(project,r) for project,ref in references.items() for r in ref['preparation_build_attempts']]
            if prep_costs:
                project,attempt=max(prep_costs,key=lambda x:x[1]['wall_seconds']); pool=attempt['wall_seconds']
                basis={'kind':'largest observed reference preparation attempt; includes project work and failures, not cache-attributable savings','project':project,'log':attempt['evidence_log']}
        if name=='Core invalidation fan-out' and inv['incremental'] and estimates.get('checkpoint',{}).get('module_mean_model_seconds') is not None:
            fanout=max(inv['incremental'],key=lambda r:r['workload_rebuilds']['checkpoint']); n=fanout['workload_rebuilds']['checkpoint']; total=inv['build_workloads']['checkpoint']['reachable_modules']
            pool=estimates['checkpoint']['module_mean_model_seconds']*n/total
            basis={'kind':'potential per-core-edit cost pool: graph affected-module fraction times checkpoint model; not observed rebuild time or savings','core':fanout['module'],'affected_modules':n,'workload_modules':total}
        changes.append({'candidate_cost_pool_seconds':pool,'evidence_basis':basis,'name':name,'change':change,'measured_target':path,'observed_target_wall_seconds':row['plain']['wall_seconds'] if row and row['status']=='pass' else None,'fresh_module_evidence':row['plain']['log'] if row and row['status']=='pass' else None,'fresh_profile_evidence':row.get('profile',{}).get('log') if row else None,'prior_evidence':'docs/audits/build-speed.md' if name in ['Mathlib/Bridge cache','DecisionGaps','OpenLoops','Horizon','RevertData','Axiom pins','Tiny module overhead'] else None,'savings_status':'candidate cost pool, not measured savings; validate with obligation-preserving A/B checks'})
    changes.sort(key=lambda r:-(r['candidate_cost_pool_seconds'] or 0))
    profile_data=read(args.profiles) if args.profiles else None
    if profile_data is not None: assert profile_data['base']==inv['base'], 'profile dataset base mismatch'
    expected_paths={r['path'] for r in inv['sample_plan'] if r.get('selection')=='size_quartile_midpoint'}
    local_complete=len(expected_paths)==40 and expected_paths<={r['path'] for r in passing} and len(comparisons)==10 and all(r['local_quartile_coverage']['complete'] for r in comparisons)
    profiled_paths={r['path'] for r in (profile_data or {}).get('profiles',[])}
    profile_missing=sorted({r['path'] for r in passing}-profiled_paths)
    profile_complete=local_complete and not profile_missing and len((profile_data or {}).get('slowest_sampled_declarations',[]))>=20
    reference_gaps=[name for name in ('EvmYul','Clear') if references.get(name,{}).get('status')!='pass']
    complete=profile_complete and not reference_gaps and len(changes)==10 and all(r['evidence_basis'] is not None for r in changes)
    result={'base':inv['base'],'status':'done' if complete else 'partial','local_sampling_complete':local_complete,'profile_coverage':{'expected':len(passing),'observed':len(profiled_paths),'missing':profile_missing,'complete':profile_complete},'reference_gaps':reference_gaps,'attempted_observations':len(attempts),'unique_current_modules':len(current),'passing_current_modules':len(passing),'failed_attempts':[{'path':r['path'],'status':r['status']} for r in attempts if r['status']!='pass'],'current_gaps':[{'path':r['path'],'status':r['status']} for r in current.values() if r['status']!='pass'],'reference_timings':references,'per_area':comparisons,'full_check_only_estimates':estimates,'incremental':inv['incremental'],'slowest_sampled_modules':sorted([{'path':r['path'],'seconds':r['plain']['wall_seconds'],'lines':r['lines'],'classification':r['classification'],'selection':r.get('selection')} for r in passing],key=lambda r:-r['seconds'])[:20],'declaration_profiles':profile_data,'ten_changes_prioritization':'heuristic ranking by explicit cost pools: modelled potential per-core-edit invalidation, reference preparation attempts, and observed module checks. These have different operation/frequency boundaries; not the ten largest demonstrated savings','ten_changes':changes,'limitations':['Targeted tails are separate from size-stratified rate estimates.','Generated source classes are marker-based; unmarked is not proven handwritten. Timing classes cover whole files; mixed generated spans are line-counted separately, not timed independently.','Full estimates are deterministic model outputs, not validated runtime bounds; named checkpoint/full/Bridge closures overlap and must not be summed. Quartiles are selected from all tracked area modules, not a random target-specific sample.','Reference build-attempt timings include dependency preparation; only complete per-project module sums are compared.','Recommendations use two dependency cost pools plus the eight slowest observed sample modules, not a global exhaustive ranking; no saving or proof-preservation implementation is claimed.']}
    args.out.mkdir(parents=True,exist_ok=True); (args.out/'analysis.json').write_text(json.dumps(result,indent=2)+'\n'); print('derived analysis',len(passing),'current passes;',len(references),'reference datasets')
if __name__=='__main__': main()
