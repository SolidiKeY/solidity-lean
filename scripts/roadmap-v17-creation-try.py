#!/usr/bin/env python3
"""Scoped published creation-try evidence consumer, never whole-profile closure."""
import hashlib
import importlib.util
import json
import re
import subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PUBLICATION='4165de133bafd522ab18099e18cad489bb1aa7d6'
LEGACY='Solidity.Examples.Tactics.CreationTrySource'
IR=LEGACY+'IR'
THEOREMS=['original_outputs','both_approx','ordinary_execution','wrong_reason_refused','collision_uncaught','actual_rollback_and_installation','actual_arguments']
REQUESTS=[(LEGACY,LEGACY+'.'+n,'theorem') for n in THEOREMS]+[(IR,IR+'.original_outputs_ir','theorem')]
REQUESTS += [(LEGACY,LEGACY+'.'+n,'definition') for n in ['both','bothOrdinary','collision','installations','argumentValues','expected']]
REQUESTS += [(IR,IR+'.bothIR','definition'),('Solidity.Tools.CreationTryReplay','Solidity.Tools.CreationTryReplay.replay','definition')]

def load_memory():
    spec=importlib.util.spec_from_file_location('creation_memory',ROOT/'scripts/roadmap-v17-memory-calls.py')
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def query_bytes():
    m=load_memory()
    source=(ROOT/'scripts/roadmap-v17-kernel-query.lean').read_text().replace('-- V17_PROJECT_IMPORTS','import '+IR)
    source+='\n'+(ROOT/'scripts/roadmap-v17-creation-try-query.lean').read_text().split('-- V17_CREATION_BODY\n',1)[1]
    names=', '.join('('+m.name_term(n)+', '+m.name_term(mod)+', '+json.dumps(kind)+')' for mod,n,kind in REQUESTS)
    source+='\nrun_cmd do\n  let result ← Lean.Elab.Command.liftTermElabM (Solidity.Roadmap.V17.KernelQuery.extract #['+names+'])\n  Lean.Elab.Command.liftIO (IO.println ("V17_CREATION_KERNEL_BEGIN\\n" ++ result.compress ++ "\\nV17_CREATION_KERNEL_END"))\n'
    source+=''.join('#print axioms '+n+'\n' for _,n,kind in REQUESTS if kind=='theorem')
    return source.encode()


def publication_identity():
    files={};fixtures={}
    paths=['Solidity/Examples/Tactics/CreationTrySource.lean','Solidity/Examples/Tactics/CreationTrySourceIR.lean','Solidity/Frontend/CreationTryImport.lean','Solidity/Tools/CreationTryReplay.lean','Solidity/Semantics/CreationTryFrame.lean','scripts/creation-try-adapter.mjs','tests/solc/CreationTry.ast.json','tests/solc/CreationTryIR.ast.json']
    for name in paths:
        actual=(ROOT/name).read_bytes()
        published=subprocess.check_output(['git','show',PUBLICATION+':'+name],cwd=ROOT,timeout=30)
        if actual!=published:raise ValueError('producer differs from publication: '+name)
        files[name]=hashlib.sha256(actual).hexdigest()
        if name.endswith('.json'):
            document=load_memory().load_kernel().e.loads(actual)
            h=document['header']; source=ROOT/h['source']
            if source.exists() and hashlib.sha256(source.read_bytes()).hexdigest()!=h['sourceSha256']:raise ValueError('local original source differs')
            fixtures[name]={'header':h,'astSha256':hashlib.sha256(json.dumps(document['ast'],sort_keys=True,separators=(',',':')).encode()).hexdigest(),'localOriginalSourceAvailable':source.exists()}
    if fixtures['tests/solc/CreationTry.ast.json']['header']['settings']['viaIR'] is not False or fixtures['tests/solc/CreationTryIR.ast.json']['header']['settings']['viaIR'] is not True:raise ValueError('wrong pipeline identity')
    return {'publication':PUBLICATION,'sourceFiles':files,'fixtures':fixtures,'scope':'Complete published creation fixture only, not whole admitted source profile','externalEvmDifferentialRun':False,'gasCreateAddressNonceEquivalence':False}


def equal(a,b):return json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True)


def observation(raw):
    v=load_memory().frame(raw,'V17_CREATION_BEGIN','V17_CREATION_END')
    fields={'schema','orderedSignatures','legacy','ordinary','viaIR','expectedLegacy','expectedIR','collision','installations','arguments','hostContext','first','second','nativeLegacy','nativeIR','semanticPremisesDischarged','releaseClosed'}
    if set(v)!=fields or type(v['schema']) is not int or v['schema']!=1 or v['semanticPremisesDischarged'] is not False or v['releaseClosed'] is not False:raise ValueError('invalid/promoted creation observation')
    if v['orderedSignatures']!=['f()','g()']:raise ValueError('wrong ordered signatures')
    expected=v['expectedLegacy']
    if not isinstance(expected,list) or len(expected)!=2 or any(not isinstance(xs,list) or len(xs)<96 or any(type(x) is not int or not 0<=x<256 for x in xs) for xs in expected):raise ValueError('missing full byte observations')
    if not all(equal(v[n],expected) for n in ['legacy','ordinary','viaIR','expectedIR']):raise ValueError('ordered actual/expected outputs disagree')
    if not equal(v['collision'],{'kind':'bare-revert','bytes':[]}) or not equal(v['installations'],[True,True]) or not equal(v['arguments'],[3,8]):raise ValueError('changed world/outcome/argument observation')
    ctx={'kind':'creation-try-source','selfAddress':'457415396813334496268612927368880745799219276745','sender':'103164821458651970696730694074090566093359944210','value':'0','ownerFunds':'0','timestamp':'0','senderFunds':'1000000000000000000000000000000','firstCreationNonce':1}
    if not equal(v['hostContext'],ctx) or v['first']!='428238858683769988117249899297947241168592284849' or v['second']!='765865378857594171345198072072138302409814020804':raise ValueError('wrong account/funding context')
    for pipeline in ['nativeLegacy','nativeIR']:
        native=v[pipeline]
        if native.get('status')!='working' or native.get('selfAddress')!=ctx['selfAddress']:raise ValueError('failed native replay')
        rows=native.get('observed')
        if not isinstance(rows,list) or len(rows)!=2:raise ValueError('missing native ordered observations')
        for i,row in enumerate(rows):
            expected_row={'signature':v['orderedSignatures'][i],'failed':False,'values':[],'returnBytes':expected[i],'revertBytes':[],'creationTarget':v[['first','second'][i]],'creationNonce':i+1,'constructorInstalled':i==1}
            if not equal(row,expected_row):raise ValueError('changed native outcome/account/rollback')
    return v


def metadata(raw):
    m=load_memory();k=m.load_kernel()
    meta=m.frame(raw,'V17_CREATION_KERNEL_BEGIN','V17_CREATION_KERNEL_END')
    if set(meta)!={'schema','rows','imports','releaseClosed'} or type(meta['schema']) is not int or meta['schema']!=1 or meta['releaseClosed'] is not False or len(meta['rows'])!=len(REQUESTS):raise ValueError('missing checked metadata')
    fields={'name','nameAst','module','kind','unsafe','partial','levels','type','value','typeDisplaySupplemental','typeDependencies','valueDependencies','axioms','binderCount','propositionBinders','semanticPremisesDischarged'}
    for row,(mod,name,kind) in zip(meta['rows'],REQUESTS):
        if set(row)!=fields or (row['name'],row['module'],row['kind'])!=(name,mod,kind) or row['nameAst']!=k.name_ast(name):raise ValueError('wrong declaration identity/shape/order')
        if row['unsafe'] is not False or row['partial'] is not False or row['semanticPremisesDischarged'] is not False:raise ValueError('unsafe/promoted declaration')
        m.check_value_evidence(row,k)
        if type(row['binderCount']) is not int or row['binderCount']<0 or row['propositionBinders']!=sorted(set(row['propositionBinders'])) or any(type(i) is not int or not 0<=i<row['binderCount'] for i in row['propositionBinders']):raise ValueError('invalid proposition binders')
        if row['axioms']!=sorted(set(row['axioms'])) or not set(row['axioms'])<={'Classical.choice','propext','Quot.sound'}:raise ValueError('unapproved declaration axiom')
    axioms={}
    for line in raw.decode().splitlines():
        if not line.startswith("'"+LEGACY):continue
        match=re.fullmatch(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",line)
        if match is None or match[1] in axioms:raise ValueError('bad/duplicate axiom print')
        axioms[match[1]]=sorted(x.strip() for x in (match[2] or '').split(',') if x.strip())
    expected={r['name']:r['axioms'] for r in meta['rows'] if r['kind']=='theorem'}
    if axioms!=expected:raise ValueError('missing/changed axiom prints')
    return meta


def verify(record,directory,current,producer=None,producer_directory=None,previous=None):
    m=load_memory();k=m.load_kernel()
    raw=m.verify_stage(k,record,directory,current,producer,producer_directory,previous,'warm-creation-try','warm-creation-try-observation')
    obs=observation(raw);meta=metadata(raw)
    m.verify_imports(k,meta,record,current,producer,IR)
    return {'metadataComplete':True,'metadata':meta,'observation':obs,'sourceSnapshot':current,'installedInputs':record['installedBefore'],'profile':publication_identity(),'semanticPremisesDischarged':False,'releaseClosed':False,'boundary':'Current warm checked fixture declarations and source-model/native replay consistency only; not clean whole-proof closure, external EVM differential or gas/nonce/address-model equivalence.'}


if __name__=='__main__':
    import argparse,fcntl
    from types import SimpleNamespace
    p=argparse.ArgumentParser(description=__doc__)
    for flag in ['report','producer','out','replay-out']:p.add_argument('--'+flag,type=Path,required=True)
    args=p.parse_args()
    try:
        m=load_memory();k=m.load_kernel()
        with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            first=verify(k.e.load(args.report),args.report.parent,k.e.snapshot(ROOT),k.e.load(args.producer),args.producer.parent)
            if k.p.collect(SimpleNamespace(gate='warm-creation-try-observation',out=args.replay_out))!=0:raise ValueError('live replay failed')
            second=verify(k.e.load(args.replay_out/'provenance.json'),args.replay_out,k.e.snapshot(ROOT),k.e.load(args.producer),args.producer.parent,previous=k.e.load(args.report))
            m.exact_replay(first,second)
            args.out.write_text(json.dumps({'verified':first,'replay':second,'exactObservationReplay':True,'semanticPremisesDischarged':False,'releaseClosed':False},indent=2)+'\n')
            print(json.dumps({'declarations':len(REQUESTS),'orderedPipelines':['legacy','viaIR'],'exactObservationReplay':True,'semanticPremisesDischarged':False,'releaseClosed':False}))
    except (ValueError,KeyError,TypeError,OSError) as error:
        print(json.dumps({'error':str(error),'releaseClosed':False}));raise SystemExit(2)
