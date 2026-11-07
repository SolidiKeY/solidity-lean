#!/usr/bin/env python3
"""Guard lexical migration labels erasing changed or absent frozen statements.

Pin exact observed pairs; retain raw signatures/context and every original row.
H19/H60 authorization explains upstream evolution, not frozen/current theorem
transport, kernel fidelity, live ownership or joint witness evidence.
"""
import argparse
from collections import Counter
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

spec=importlib.util.spec_from_file_location('original_current_census',Path(__file__).with_name('current_dependencies.py'))
current=importlib.util.module_from_spec(spec);spec.loader.exec_module(current)
ROOT=current.ROOT
PINS=ROOT/'tests/h62/item2/audit-readonly-calls/signature-drift-pins.json'
DECISIONS_SHA='5e4335f38abb74a8864863577b04363980659e6b92a4a9835e8a0efa5bd833dd'
DEFINITIONS=['Solidity/Source/Monetary.lean','Solidity/Source/Types.lean','Solidity/Source/Typing.lean','Solidity/Source/Machine.lean','docs/feature-work/balances-fit.md']


def context(row):return current.digest({k:row[k] for k in ['variable_context','visibility']})


def matches(old,now,pin):
    if pin['original_signature_sha256']!=old['signature_sha256'] or pin['original_context_sha256']!=context(old):return False
    if now is None:return pin['kind']=='removed-private-identity' and 'private' in old['visibility'] and pin['observed_signature_sha256'] is None and pin['observed_context_sha256'] is None
    if pin['observed_signature_sha256']!=now['signature_sha256'] or pin['observed_context_sha256']!=context(now):return False
    replacements={'H19-balance-projection':('.balance.val','.balance'),'H19-balance-domain':('(b : Word)','(b : Monetary.Balance)'),'H60-typing-parameter':('E.isBase ','E.isBase E.mapFree ')}
    pair=replacements.get(pin['kind'])
    return bool(pair and old['signature']!=now['signature'] and old['signature'].replace(*pair)==now['signature'] and context(old)==context(now))


def dossier(frozen,rows,pins):
    indexed={(r['file'],r['source_name']):r for r in rows}
    if len(indexed)!=len(rows):raise ValueError('duplicate current declaration')
    policy={(r['file'],r['source_name']):r for r in pins['cases']}
    if len(policy)!=len(pins['cases']):raise ValueError('duplicate observed pair')
    keys={(r['file'],r['source_name']) for r in frozen['declarations']}
    if len(keys)!=792 or len(frozen['declarations'])!=792:raise ValueError('original 792 membership mismatch')
    if not set(policy)<=keys:raise ValueError('foreign observed pair')
    observed=current.original.fidelity.compare(frozen['declarations'],rows)
    changes=[];all_rows=[]
    states={(r['file'],r['source_name']):r['source_status'] for r in observed['original_obligations']}
    for old in frozen['declarations']:
        key=(old['file'],old['source_name']);now=indexed.get(key);state=states[key]
        row={'file':key[0],'source_name':key[1],'source_status':state,'historical_owner':old['owner'],'historical_witness_status':old['witness_status'],
             'current_kernel_fidelity':'pending','live_ownership':'unverified','original_obligation_discharged':False}
        all_rows.append(row)
        if state=='lexical-header-retained':continue
        recorded=key in policy and matches(old,now,policy[key])
        old_fields={k:old[k] for k in ['signature','signature_sha256','variable_context','visibility','kernel_name']}
        new_fields={k:now[k] for k in ['signature','signature_sha256','variable_context','visibility','kernel_name']} if now else None
        changes.append({**row,'original':old_fields,'current':new_fields,'lexical_review':policy[key]['kind'] if recorded else 'unreviewed-drift',
                        'exact_observed_pair':recorded,'signature_diff':list(difflib.unified_diff(old['signature'].splitlines(),now['signature'].splitlines() if now else [],fromfile='original',tofile='current',lineterm='')),
                        'statement_transport':'pending; lexical matching and model-repair authorization do not prove frozen/current correspondence'})
    return {'schema':1,'original_base':current.headers.BASE,'original_obligations':792,'original_rows':all_rows,'changes':changes,
            'source_statuses':observed['source_statuses'],'lexical_review_counts':dict(Counter(r['lexical_review'] for r in changes)),
            'recorded_pairs_now_retained':[list(key) for key in sorted(policy) if states[key]=='lexical-header-retained'],
            'added_declarations':observed['added_declarations'],'original_obligations_discharged':0,'runtime_gate_pass':False,
            'boundary':'Lexical signature/context review only. No semantic weakening/equivalence verdict, new premise or exclusion, kernel fidelity, live ownership or witness credit.'}


def read_pairs(path):
    raw=path.read_bytes()
    return raw,hashlib.sha256(raw).hexdigest(),json.loads(raw,object_pairs_hook=current.original.pairs)


def run(output,reviewed,decisions):
    if not output.is_absolute():raise ValueError('absolute output required')
    frozen=current.original.load_pinned(reviewed,current.REVIEWED_SHA);current.verify_frozen(frozen)
    raw_decisions=decisions.read_bytes()
    if hashlib.sha256(raw_decisions).hexdigest()!=DECISIONS_SHA:raise ValueError('coordinator decision input hash mismatch')
    decision_rows=[line for line in raw_decisions.decode().splitlines() if line.startswith('- H19 ') or ' H60 (user)' in line]
    if len(decision_rows)!=2:raise ValueError('missing H19/H60 decision records')
    output.mkdir(mode=0o700,exist_ok=False);sources=output/'sources';sources.mkdir()
    receipt={'schema':1,'status':'failed','steps':[],'original_base':current.headers.BASE,'reviewed_sha256':current.REVIEWED_SHA,'decisions_sha256':DECISIONS_SHA}
    try:
        head=current.headers.git('rev-parse','HEAD').decode().strip();paths=sorted(set([m['file'] for m in frozen['modules']]+DEFINITIONS))
        captured={};rows=[];tool_paths=[*current.SCANNER.glob('*.py'),*Path(__file__).parent.glob('*.py')]
        tools={str(p):current.headers.binder.sha(p) for p in tool_paths}
        pin_raw,pin_digest,pins=read_pairs(PINS);tools[str(PINS)]=pin_digest
        if pins['schema']!=1 or pins['original_base']!=current.headers.BASE:raise ValueError('wrong pair observation schema/base')
        for path in paths:
            file=ROOT/path
            if file.resolve()!=file:raise ValueError('source alias refused')
            raw=file.read_bytes();blob=current.headers.git('rev-parse',head+':'+path).decode().strip()
            if current.headers.blob_hash(raw)!=blob:raise ValueError('working source differs from captured commit')
            dest=sources/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw);captured[path]={'sha256':hashlib.sha256(raw).hexdigest(),'git_blob':blob}
            if path in {m['file'] for m in frozen['modules']}:rows.extend(current.original.census.declarations_text(path,raw.decode()))
        result=dossier(frozen,rows,pins);result.update(source_head=head,decision_context=decision_rows,observed_pair_pins_sha256=hashlib.sha256(pin_raw).hexdigest(),source_sha256=captured)
        for path,pin in captured.items():
            if current.headers.binder.sha(ROOT/path)!=pin['sha256'] or current.headers.binder.sha(sources/path)!=pin['sha256']:raise ValueError('source changed during review capture')
        for path,pin in tools.items():
            if current.headers.binder.sha(Path(path))!=pin:raise ValueError('tool or pair observation drift')
        current.original.load_pinned(reviewed,current.REVIEWED_SHA)
        if hashlib.sha256(decisions.read_bytes()).hexdigest()!=DECISIONS_SHA or current.headers.git('rev-parse','HEAD').decode().strip()!=head:raise ValueError('decision/head drift')
        (output/'dossier.json').write_text(json.dumps(result,sort_keys=True,ensure_ascii=False,indent=2)+'\n')
        (output/'decisions.txt').write_bytes(raw_decisions);(output/'observed-pairs.json').write_bytes(pin_raw)
        receipt.update(status='pass',source_head=head,tools_sha256=tools,captured_sources=captured,dossier_sha256=current.headers.binder.sha(output/'dossier.json'),
                       source_statuses=result['source_statuses'],lexical_review_counts=result['lexical_review_counts'],original_obligations_discharged=0,
                       project_code_loaded=False,lean_executed=False,boundary=result['boundary'])
    except Exception as exc:receipt['error']=str(exc);raise
    finally:(output/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--reviewed',type=Path,required=True);p.add_argument('--decisions',type=Path,required=True);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    try:
        with current.headers.binder.writer_lease():result=run(args.output,args.reviewed,args.decisions)
    except (OSError,ValueError,subprocess.SubprocessError) as exc:p.exit(1,'SIGNATURE_DRIFT_CAPTURE_REJECT: '+str(exc)+'\n')
    print('SIGNATURE_DRIFT_CAPTURE_PASS '+json.dumps({k:result[k] for k in ['source_head','source_statuses','lexical_review_counts','original_obligations_discharged']}))


if __name__=='__main__':main()
