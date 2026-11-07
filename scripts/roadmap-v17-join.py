#!/usr/bin/env python3
"""Join producer accounting to live replayed kernel metadata; never close features."""
import argparse
import fcntl
import importlib.util
import json
import re
from pathlib import Path
import subprocess
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('v17_join_kernel',ROOT/'scripts/roadmap-v17-kernel.py')
k=importlib.util.module_from_spec(spec); spec.loader.exec_module(k)
e=k.e
FIELDS={'name','module','kind','typeSha256','valueSha256','typeDependencies','valueDependencies','typeProjectionDependencies','valueProjectionDependencies','axioms','binderCount','propositionBinders'}


def joined(report,ledger,current,imports,bindings,rows):
    """rows is internal validated/replayed output, never read from producer JSON."""
    e.require(type(report['schema']) is int and report['schema']==1,'invalid producer schema')
    e.closure(report,ledger,current['revision'],imports)  # Preserve the old producer-only mode.
    for flag in ('releaseClosed','semanticPremisesDischarged'):
        e.require(report.get(flag,False) is False,'producer attempts semantic closure')
    e.require(type(bindings['schema']) is int and bindings['schema']==1 and set(bindings)=={'schema','snapshot','declarations'},'invalid binding schema')
    e.require(k.canonical(bindings['snapshot'])==k.canonical(current),'binding source/tree/toolchain/config differs')
    claims={t['name']:t for t in report['theorems']}; bound={}
    for b in bindings['declarations']:
        e.require(set(b)=={'declaration','accountedPropositionBinders'},'unexpected declaration binding')
        d=b['declaration']; e.require(set(d)==FIELDS,'missing exact declaration/type/dependency binding')
        name=d['name']; e.require(name in claims and name not in bound,'unknown/duplicate theorem binding')
        a=b['accountedPropositionBinders']
        e.require(isinstance(a,list) and all(type(i) is int and i>=0 for i in a) and a==sorted(set(a)),'invalid proposition binder accounting')
        bound[name]=b
    results=[]
    for name,t in claims.items():
        e.require(t.get('semanticPremisesDischarged',False) is False and t.get('releaseClosed',False) is False,'theorem attempts semantic closure')
        obligations=['semantic-feature-match-unreviewed','semantic-premises-not-discharged']
        e.require(all(isinstance(o,str) for o in t['observations']),'invalid producer observation')
        row=rows.get(name); binding=bound.get(name); matched=False
        if binding is None: obligations.append('missing-exact-declaration-binding')
        if row is None: obligations.append('missing-current-checked-declaration-evidence')
        if row is not None:
            e.require(t['module']==row['module'] and t['axioms']==row['axioms'],'producer defining module/axioms disagree with kernel')
            e.require(t['kind']!='external-test','external observation cannot be kernel proof')
            e.require(t['kind']!='kernel' or row['kind']=='theorem','definition/contract claimed as kernel theorem')
            if row['propositionBinders']: obligations.append('conditional-declaration')
            if row['kind']!='theorem': obligations.append('definition-or-component-contract')
            if binding is not None:
                e.require(k.canonical(binding['declaration'])==k.canonical({field:row[field] for field in FIELDS}),'wrong checked name/module/kind/type/dependencies/axioms')
                accounted=binding['accountedPropositionBinders']
                e.require(set(accounted)<=set(row['propositionBinders']),'invented proposition binder accounting')
                if set(row['propositionBinders'])-set(accounted): obligations.append('unaccounted-proposition-binders')
                matched=True
        if t['premises']: obligations.append('producer-named-premises-not-discharged')
        if t['observations']: obligations.append('producer-observations-unverified')
        results.append({'name':name,'declarationEvidenceMatched':matched,'kind':row['kind'] if row else None,
                        'propositionBinders':row['propositionBinders'] if row else None,
                        'unaccountedPropositionBinders':sorted(set(row['propositionBinders'])-set(binding['accountedPropositionBinders'])) if row and binding else (row['propositionBinders'] if row else None),
                        'producerPremises':t['premises'],'unverifiedObservations':t['observations'],
                        'obligations':obligations,'semanticPremisesDischarged':False})
    e.require(set(rows)<=set(claims),'unmatched extracted declarations')
    feature_rows=[]
    for claim in report['claims']:
        e.require(claim.get('semanticPremisesDischarged',False) is False and claim.get('releaseClosed',False) is False,'feature row attempts semantic closure')
        e.require(claim['status']!='done','feature closure requires independent semantic review; declaration metadata cannot promote rows')
        e.require(all(n in claims for n in claim['theorems']),'unknown feature theorem reference')
        e.require(isinstance(claim['observations'],list) and all(isinstance(o,str) for o in claim['observations']),'invalid feature observation')
        declared={o for n in claim['theorems'] for o in claims[n]['observations']}
        feature_rows.append({'id':claim['id'],'producerStatus':claim['status'],'semanticFeatureMatch':'unreviewed',
                             'unverifiedObservations':claim['observations'],'unmatchedProducerObservations':[o for o in claim['observations'] if o not in declared],
                             'obligations':['semantic-feature-match-unreviewed','observations-not-independently-verified'],'semanticPremisesDischarged':False})
    required=e.inventory(ledger)
    return {'schema':1,'revision':current['revision'],'sourceTree':current['sourceTree'],
            'sourceToolchainKey':current['sourceToolchainKey'],'ledgerSha256':report['ledgerSha256'],
            'declarations':results,'requiredRows':len(required),'openRows':required,
            'featureEvidenceAccounting':feature_rows,'producerClaims':report['claims'],'missingProducerRows':sorted(set(required)-{r['id'] for r in report['claims']}),
            'accountingComplete':False,'semanticPremisesDischarged':False,'releaseClosed':False,
            'boundary':'Live declaration metadata join only; no semantic feature/observation sufficiency or premise discharge.'}


def live_rows(manifest,current,out):
    e.require(set(manifest)=={'schema','snapshot','records'} and type(manifest['schema']) is int and manifest['schema']==1,'invalid record manifest')
    e.require(k.canonical(manifest['snapshot'])==k.canonical(current),'record manifest revision/tree/tool/input differs')
    e.require(isinstance(manifest['records'],list) and len(manifest['records'])<=16,'too many module records')
    rows={}; modules=set(); receipts=[]
    for i,ref in enumerate(manifest['records']):
        e.require(set(ref)=={'path','sha256'},'invalid record reference')
        path=Path(ref['path'])
        e.require(path.is_absolute() and path.resolve()==path and path.is_relative_to('/workspace') and not path.is_relative_to(ROOT),'invalid retained record path')
        raw=path.read_bytes(); e.require(e.digest(raw)==ref['sha256'],'corrupt retained record')
        old=e.loads(raw)
        e.require(k.canonical(old['before'])==k.canonical(current) and k.canonical(old['after'])==k.canonical(current),'nonexact retained snapshot')
        req=k.validate_record(old,current)
        e.require(req['module'] not in modules,'duplicate module record'); modules.add(req['module'])
        replay=k.collect(req,out/('replay-'+str(i)))
        e.require(replay['exit']==0,'live kernel replay failed')
        k.validate_record(replay,e.snapshot(ROOT)); k.match_replay(old,replay)
        e.require(path.read_bytes()==raw,'retained record changed during replay')
        k.validate_record(old,current)
        for row in replay['result']['rows']:
            e.require(row['name'] not in rows,'duplicate extracted declaration'); rows[row['name']]=row
        receipts.append({'record':ref,'replay':str(out/('replay-'+str(i))/'record.json'),'module':req['module']})
    return rows,receipts


def catalog(current, ledger):
    families=[]
    for label in ('contracts','compiler'):
        path=ROOT/('tests/roadmap-v17/requests/'+label+'.json'); req=k.request(e.load(path))
        source=ROOT/(req['module'].replace('.','/')+'.lean'); raw=source.read_bytes(); declarations=[]
        for item in req['declarations']:
            hits=[]
            for line,text in enumerate(raw.decode().splitlines(),1):
                match=re.match(r'^(theorem|def) ([A-Za-z_][A-Za-z0-9_.]*)[ {(:]',text)
                if match and item['name'].endswith('.'+match[2]) and (match[1]=='theorem')==(item['kind']=='theorem'):
                    hits.append({'line':line,'text':text})
            e.require(len(hits)==1,'ambiguous/missing source-only declaration: '+item['name'])
            start=hits[0]['line']-1; context='\n'.join(raw.decode().splitlines()[start:start+32])
            e.require(':=' in context,'bounded source header unavailable')
            header=context.split(':=',1)[0]+':='
            declarations.append({**item,'sourceHeader':header,'sourceDeclaration':hits[0],'checkedEvidence':'missing-until-current-live-validation','semanticFeatureMatches':[]})
        families.append({'request':req,'requestSha256':e.digest(path.read_bytes()),'source':str(source.relative_to(ROOT)),
                         'sourceSha256':e.digest(raw),'declarations':declarations})
    return {'schema':1,'snapshot':current,'families':families,'ledger':ledger,
            'ledgerSha256':e.digest(json.dumps(ledger,sort_keys=True).encode()),'openRows':e.inventory(ledger),
            'semanticMatchesRequireIndependentReview':True,'semanticPremisesDischarged':False,'releaseClosed':False,
            'boundary':'Source-only request discovery, not checked declarations or theorem-to-feature matches.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalog',action='store_true')
    for name in ('producer','bindings','records'): parser.add_argument('--'+name,type=Path)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args(); out=args.out
    e.require(out.is_absolute() and out.resolve()==out and out.is_relative_to('/workspace') and not out.is_relative_to(ROOT) and not out.exists(),'new external output directory required')
    with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB); k.p.ensure_no_unresolved(); out.mkdir(parents=True)
        current=e.snapshot(ROOT)
        if args.catalog:
            result=catalog(current,e.load(ROOT/e.LEDGER)); e.require(e.snapshot(ROOT)==current,'source/tool changed during catalog')
            (out/'catalog.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps({'requestedDeclarations':sum(len(f['declarations']) for f in result['families']),'openRows':len(result['openRows']),'releaseClosed':False})); return 0
        e.require(args.producer and args.bindings and args.records,'producer/bindings/records required')
        inputs={name:getattr(args,name).read_bytes() for name in ('producer','bindings','records')}
        for name,raw in inputs.items(): (out/(name+'.json')).write_bytes(raw)
        manifest=e.loads(inputs['records']); rows,receipts=live_rows(manifest,current,out)
        imports=e.loads(subprocess.check_output(['node',str(ROOT/'scripts/roadmap-v17-imports.mjs')],cwd=ROOT,timeout=60))['modules']
        result=joined(e.loads(inputs['producer']),e.load(ROOT/e.LEDGER),current,imports,e.loads(inputs['bindings']),rows)
        e.require(e.snapshot(ROOT)==current,'source/tool/config changed during join')
        e.require(all(getattr(args,n).read_bytes()==raw for n,raw in inputs.items()),'producer/bindings/records changed during join')
        for ref in manifest['records']:
            raw=Path(ref['path']).read_bytes(); e.require(e.digest(raw)==ref['sha256'],'retained record changed during join')
            k.validate_record(e.loads(raw),current)
        result['receipts']=receipts; result['inputSha256']={n:e.digest(raw) for n,raw in inputs.items()}
        (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({'declarationsMatched':sum(d['declarationEvidenceMatched'] for d in result['declarations']),'openRows':result['requiredRows'],'semanticPremisesDischarged':False,'releaseClosed':False})); return 0


if __name__=='__main__':
    try: raise SystemExit(main())
    except (ValueError,KeyError,TypeError,OSError,RecursionError,subprocess.SubprocessError) as error:
        print(json.dumps({'error':str(error),'semanticPremisesDischarged':False,'releaseClosed':False})); raise SystemExit(2)
