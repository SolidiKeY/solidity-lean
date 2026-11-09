#!/usr/bin/env python3
"""Attribute Firefox traces without adding overlapping nested spans.
python3 .../profiles.py --sample EXTERNAL/sample-results.json --out DIR
Rank sampled declarations only. Durations are unions of observed attributed wall
intervals, not additive CPU costs. Missing sub-threshold events are unknown.
"""
import argparse,collections,json,pathlib,re,sys
sys.dont_write_bytecode=True
from audit import strip_comments

def union_seconds(intervals):
    merged=[]
    for start,end in sorted(intervals):
        if merged and start<=merged[-1][1]: merged[-1][1]=max(end,merged[-1][1])
        else: merged.append([start,end])
    return sum(b-a for a,b in merged)/1000

def cumulative_components(log):
    """Lean's basic profiler totals; not a partition of process wall time."""
    text=pathlib.Path(log).read_text()
    if 'cumulative profiling times:' not in text: return None
    totals={}
    for line in text.rsplit('cumulative profiling times:',1)[1].splitlines():
        m=re.fullmatch(r'\s+(.+?)\s+([0-9.]+)(ns|μs|µs|us|ms|s)\s*',line)
        if m: totals[m[1]]=float(m[2])*{'ns':1e-9,'μs':1e-6,'µs':1e-6,'us':1e-6,'ms':1e-3,'s':1}[m[3]]
    return totals

def explicit_target(name):
    m=re.search(r'elaborating proof of ([^\s]+)',name)
    if m: return m[1]
    m=re.search(r'typechecking declarations \[([^\]]+)\]',name)
    if m: return m[1] if ',' not in m[1] else 'declaration_group:['+m[1]+']'
    return None

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--sample',type=pathlib.Path,required=True); ap.add_argument('--extra',type=pathlib.Path,action='append',default=[]); ap.add_argument('--out',type=pathlib.Path,required=True); args=ap.parse_args()
    sample=json.loads(args.sample.read_text()); current={r['path']:r for r in sample['samples']}
    for path in args.extra:
        extra=json.loads(path.read_text()); assert extra['base']==sample['base'] and extra['versions']==sample['versions'], 'profile input base/toolchain mismatch'
        current.update({r['path']:r for r in extra['samples']})
    sample['samples']=list(current.values()); declarations=[]; profiles=[]
    for row in sample['samples']:
        profile=row.get('profile')
        if not profile or profile['exit_code']!=0: continue
        paths=[a.split('=',1)[1] for a in profile['command'] if a.startswith('-Dtrace.profiler.output=')]
        if not paths or not pathlib.Path(paths[0]).exists(): continue
        data=json.loads(pathlib.Path(paths[0]).read_text()); intervals=collections.defaultdict(list); categories=collections.defaultdict(lambda:collections.defaultdict(list)); module_categories=collections.defaultdict(list)
        known={target for thread in data['threads'] for name in thread['stringArray'] if (target:=explicit_target(name)) and not target.startswith('declaration_group:')}
        unmapped=0
        for thread in data['threads']:
            strings=thread['stringArray']; stacks=thread['stackTable']; frames=thread['frameTable']; funcs=thread['funcTable']; samples=thread['samples']; ancestry={}
            def labels(stack):
                if stack is None: return []
                chain=[]; current=stack
                while current is not None and current not in ancestry:
                    chain.append(current); current=stacks['prefix'][current]
                base=ancestry.get(current,[])
                for index in reversed(chain):
                    name=strings[funcs['name'][frames['func'][stacks['frame'][index]]]]
                    base=base+[name]; ancestry[index]=base
                return ancestry[stack]
            for stack,end,weight in zip(samples['stack'],samples['time'],samples['weight']):
                if weight<=0: continue
                names=labels(stack); interval=(end-weight,end)
                for family in ('Kernel','Meta.Tactic.simp','Meta.Tactic.bvDecide','Meta.Tactic.decide','Meta.synthInstance','Elab.async'):
                    if any(name.startswith(family+':') or name.startswith(family+'.') for name in names): module_categories[family].append(interval)
                for tactic in ('simp','decide','nativeDecide','bvDecide','rfl'):
                    if any(name.startswith('Elab.step: Lean.Parser.Tactic.'+tactic+':') for name in names): module_categories['tactic_command_'+tactic].append(interval)
                command_texts=[strip_comments(name) for name in names if name.startswith('Elab.command:')]
                if any('#eval' in name for name in command_texts): module_categories['eval_commands'].append(interval)
                if any('#print axioms' in name for name in command_texts): module_categories['axiom_pin_commands'].append(interval)
                target=next((x for name in reversed(names) if (x:=explicit_target(name))),None)
                if target is None:
                    for name in names:
                        if not name.startswith('Elab.command:'): continue
                        m=re.search(r'\b(?:theorem|lemma|def|abbrev|opaque|instance)\s+([^\s({:]+)',strip_comments(name))
                        if not m: continue
                        short=m[1].removeprefix('_root_.'); matches=[k for k in known if k==short or k.endswith('.'+short)]
                        target=matches[0] if len(matches)==1 else row['path']+'::'+short
                        break
                if target is None: unmapped+=1; continue
                interval=(end-weight,end); intervals[target].append(interval)
                for family in ('Kernel','Meta.Tactic.simp','Meta.Tactic.bvDecide','Meta.Tactic.decide','Meta.synthInstance','Elab.async'):
                    if any(name.startswith(family+':') or name.startswith(family+'.') for name in names): categories[target][family].append(interval)
        for target,spans in intervals.items():
            declarations.append({'path':row['path'],'declaration':target,'attributed_wall_seconds':union_seconds(spans),'profile_categories_seconds':{k:union_seconds(v) for k,v in categories[target].items()},'auxiliary_lean_declaration':bool(re.search(r'\._(?:proof|match|lambda)_',target)),'name_resolution':'source-command name only' if '::' in target else 'qualified trace name'})
        profiles.append({'basic_profiler_cumulative_seconds':cumulative_components(profile['log']),'component_boundary':'Lean basic-profiler cumulative totals are reported as emitted; do not subtract their sum from wall time or equate blocked time to CPU. Structured categories are inclusive lower bounds; untraced work is unknown.','path':row['path'],'profile_wall_seconds':profile['wall_seconds'],'source_classification':row['classification'],'module_category_wall_seconds_lower_bounds':{name:union_seconds(spans) for name,spans in module_categories.items()},'threshold_options':[a for a in profile['command'] if 'threshold=' in a],'unattributed_slices':unmapped})
    declarations.sort(key=lambda r:-r['attributed_wall_seconds'])
    result={'base':sample['base'],'method':'union of time-weight slices attributed by qualified async-proof/kernel trace names or matching command-source names; nested and cross-thread overlaps for a declaration merged; inclusive wall spans can overlap across declarations and MUST NOT be summed as module or CPU time; grouped mutual declarations remain groups; only sampled profiled modules ranked; below-threshold detail unknown','profiles':profiles,'declarations_profiled':len(declarations),'slowest_sampled_declarations':declarations[:20]}
    args.out.mkdir(parents=True,exist_ok=True); (args.out/'profiles.json').write_text(json.dumps(result,indent=2)+'\n'); print('profiled declarations',len(declarations))
if __name__=='__main__': main()
