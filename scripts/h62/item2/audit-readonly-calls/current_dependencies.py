#!/usr/bin/env python3
"""Guard unchanged statement headers hiding changed declared dependencies.

Fresh compiler-parsed headers are inert source observations. Preserve all frozen
obligations, reviewed historical classifications and unknown/private rows; never
promote a closure fingerprint to kernel fidelity, ownership or witness evidence.
"""
import argparse
from collections import Counter, deque
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
SCANNER=ROOT/'scripts/h62/item1/duplication-scanner'
sys.path.insert(0,str(SCANNER))
import header_dependencies as headers
spec=importlib.util.spec_from_file_location('original_obligation_join',Path(__file__).with_name('obligation_dependencies.py'))
original=importlib.util.module_from_spec(spec);spec.loader.exec_module(original)
# Exact reviewed ledger retained by the preceding capture-composition checkpoint.
REVIEWED_SHA='6f3ca3ddafba20d2f1aab9f267d4083300a36798d89cbe6bfa67e8c12c13edbb'
BOUNDARY='Declared source-closure observations only; no current kernel fidelity, body elaboration/equivalence, joint witnesses, live ownership, dynamic dependencies or timing-hold clearance. All original obligations retained.'


def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()


def unique(rows,key):
    result={r[key]:r for r in rows}
    if len(result)!=len(rows):raise ValueError('duplicate '+key)
    return result


def base_blobs():
    result={}
    for entry in headers.git('ls-tree','-rz',headers.BASE).split(b'\0'):
        if entry:
            meta,name=entry.split(b'\t',1);mode,kind,blob=meta.decode().split()
            result[name.decode()]={'mode':mode,'kind':kind,'blob':blob}
    return result


def closure(nodes,target,baseline):
    index=unique(nodes,'path');todo=deque([target]);seen=set();records=[];unknown=[];changed=[];added=[]
    while todo:
        path=todo.popleft()
        if path in seen:continue
        seen.add(path);node=index.get(path)
        if node is None:
            records.append({'path':path,'status':'missing-target-or-project-source'})
            unknown.append(path);continue
        # Include complete source hashes AND exact declared flags/resolutions.
        record={k:node.get(k) for k in ['path','module','git_blob','source_sha256','header_sha256','status','imports','error','diagnostics']}
        records.append(record)
        old=baseline.get(path)
        if old is None:added.append(path)
        elif old['kind']!='blob' or old['mode'] not in ('100644','100755') or old['blob']!=node.get('git_blob'):changed.append(path)
        if node['status']!='parsed-header':unknown.append(path)
        for item in node['imports']:
            resolution=item['resolution']
            if resolution['status']=='project-source':todo.append(resolution['path'])
            elif resolution['status']!='sdk-artifact-observed-not-loaded':
                unknown.append({'source':path,'import':item})
    records.sort(key=lambda r:r['path'])
    return {'target':target,'declared_source_nodes':len(records),'fingerprint':digest(records),
            'records':records,'changed_since_original_base':sorted(changed),'added_since_original_base':sorted(added),
            'unresolved':unknown,'complete_declared_observation':not unknown,'timing_hold':'retained',
            'kernel_fidelity':'pending','live_ownership':'unverified'}


def account(frozen,graph,current,baseline):
    # Reuse exact 129/792 membership, signature-context and unknown-path controls.
    joined=original.join(frozen,graph,current)
    unique(graph['nodes'],'path')
    targets=[r['file'] for r in frozen['modules']]
    recomputed=headers.target_records(graph['nodes'],targets)
    supplied=unique(graph['targets'],'target')
    if any(supplied[r['target']]!=r for r in recomputed):raise ValueError('declared dependency path/report mismatch')
    observations={name:closure(graph['nodes'],name,baseline) for name in sorted(targets)}
    counts=Counter(r['file'] for r in frozen['declarations'])
    for name in observations:observations[name]['original_declarations']=counts[name]
    rows=[]
    for row in joined['rows']:
        path=row['frozen']['file']
        rows.append({'frozen':row['frozen'],'current_lexical_status':row['current_lexical_status'],
                     'current_declared_dependency':supplied[path],
                     'closure_fingerprint':observations[path]['fingerprint'],
                     'current_kernel_fidelity':'pending','live_ownership':'unverified','timing_hold':'retained'})
    return {'schema':1,'kind':'fresh-original-obligation-source-dependency-ledger','boundary':BOUNDARY,
            'original_base':headers.BASE,'source_head':graph['source_head'],'original_obligations':len(rows),
            'reviewed_historical_statuses':dict(Counter(r['frozen']['witness_status'] for r in rows)),
            'current_lexical_statuses':joined['lexical_statuses'],'added_named_declarations':joined['added_declarations'],
            'modules':[observations[name] for name in sorted(observations)],'rows':rows,
            'module_dependency_statuses':dict(Counter(r['status'] for r in graph['targets'])),
            'original_obligations_discharged':0,'runtime_gate_pass':False}


def verify_frozen(frozen):
    paths,map_hash=headers.frozen_targets()
    if sorted(r['file'] for r in frozen['modules'])!=paths or frozen['map_sha256']!=map_hash:raise ValueError('frozen map identity mismatch')
    actual=[r for path in paths for r in original.census.declarations_text(path,headers.git('show',headers.BASE+':'+path).decode())]
    expected={(r['file'],r['source_name']):r for r in actual}
    seen=set()
    for row in frozen['declarations']:
        key=(row['file'],row['source_name'])
        if key in seen or key not in expected:raise ValueError('frozen declaration identity mismatch')
        seen.add(key)
        if any(row[k]!=expected[key][k] for k in ['signature','signature_sha256','variable_context','visibility']):raise ValueError('frozen signature/context mismatch')
    if len(seen)!=792 or seen!=set(expected):raise ValueError('frozen declaration coverage mismatch')


def authenticate_capture(path,capture):
    if capture.get('status')!='pass':raise ValueError('unsuccessful header capture')
    expected=hashlib.sha256((json.dumps(capture,indent=2)+'\n').encode()).hexdigest()
    original.load_pinned(path,expected)
    return expected


def run(output,reviewed):
    if not output.is_absolute():raise ValueError('absolute output required')
    frozen=original.load_pinned(reviewed,REVIEWED_SHA);verify_frozen(frozen)
    output.mkdir(mode=0o700,exist_ok=False)
    tools=[*SCANNER.glob('*.py'),*Path(__file__).parent.glob('*.py')]
    pins={str(p):headers.binder.sha(p) for p in tools}
    receipt={'schema':1,'status':'failed','kind':'fresh-original-dependency-census','reviewed_sha256':REVIEWED_SHA,'tools_sha256':pins}
    try:
        capture=headers.run(output/'headers')
        capture_sha=authenticate_capture(output/'headers/receipt.json',capture)
        graph=original.load_pinned(output/'headers/inventory.json',capture['inventory_sha256'])
        nodes=unique(graph['nodes'],'path');current=[];inputs={}
        for module in frozen['modules']:
            path=module['file'];node=nodes.get(path)
            if node is None:continue
            if node['status']!='parsed-header':raise ValueError('current target source unavailable: '+path)
            file=ROOT/path;raw=file.read_bytes()
            if file.resolve()!=file or hashlib.sha256(raw).hexdigest()!=node['source_sha256']:raise ValueError('target source drift')
            inputs[path]=raw;current.extend(original.census.declarations_text(path,raw.decode()))
        result=account(frozen,graph,current,base_blobs())
        if headers.git('rev-parse','HEAD').decode().strip()!=graph['source_head']:raise ValueError('head drift')
        for node in graph['nodes']:
            if 'source_sha256' in node and headers.binder.sha(ROOT/node['path'])!=node['source_sha256']:raise ValueError('closure source drift')
        for path,raw in inputs.items():
            if (ROOT/path).read_bytes()!=raw:raise ValueError('target changed during accounting')
        for path,pin in pins.items():
            if headers.binder.sha(Path(path))!=pin:raise ValueError('tool drift')
        original.load_pinned(reviewed,REVIEWED_SHA)
        original.load_pinned(output/'headers/receipt.json',capture_sha)
        original.load_pinned(output/'headers/inventory.json',capture['inventory_sha256'])
        headers.binder.verify_process_logs(capture['steps'])
        fixture=original.load_pinned(output/'headers/fixtures/receipt.json',capture['fixture_receipt_sha256'])
        headers.binder.verify_process_logs(fixture['steps'])
        for observed in graph['sdk_artifacts_observed_not_loaded']:
            if headers.binder.observer.regular_hash(Path(observed['path']))!=observed:raise ValueError('observed SDK artifact drift')
        if headers.binder.sha(ROOT/'lakefile.toml')!=graph['scope']['config_sha256']:raise ValueError('core configuration drift')
        (output/'ledger.json').write_text(json.dumps(result,sort_keys=True,indent=2,ensure_ascii=False)+'\n')
        receipt.update(status='pass',header_receipt_sha256=capture_sha,ledger_sha256=headers.binder.sha(output/'ledger.json'),
                       source_head=graph['source_head'],original_obligations=792,current_lexical_statuses=result['current_lexical_statuses'],
                       reviewed_historical_statuses=result['reviewed_historical_statuses'],module_dependency_statuses=result['module_dependency_statuses'],
                       original_obligations_discharged=0,inventoried_project_code_loaded=False,boundary=BOUNDARY)
    except Exception as exc:receipt['error']=str(exc);raise
    finally:(output/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--reviewed',type=Path,required=True);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    try:
        with headers.binder.writer_lease():result=run(args.output,args.reviewed)
    except (OSError,ValueError,subprocess.SubprocessError) as exc:p.exit(1,'CURRENT_DEPENDENCY_CENSUS_REJECT: '+str(exc)+'\n')
    print('CURRENT_DEPENDENCY_CENSUS_PASS '+json.dumps({k:result[k] for k in ['source_head','original_obligations','current_lexical_statuses','reviewed_historical_statuses','module_dependency_statuses']}))


if __name__=='__main__':main()
