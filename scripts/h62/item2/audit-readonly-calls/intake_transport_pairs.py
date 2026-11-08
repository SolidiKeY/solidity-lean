#!/usr/bin/env python3
"""Guard lexical version pairs being promoted to H57 or kernel/proof transport.

Execute the published Source producer, bind every supplied case to its original
792-row identity/type reference, and retain all unselected obligations. This is
source/provenance intake only; no Lean, ownership or original credit is inferred.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import importlib.machinery
import json
from pathlib import Path
import subprocess
ROOT=Path(__file__).resolve().parents[4]
PRODUCER=ROOT/'scripts/h62/item2/audit-v10-storage/transport_pairs.py'
SCANNER=ROOT/'scripts/h62/item2/audit-readonly-calls/census.py'
PINS=ROOT/'tests/h62/item2/audit-readonly-calls/signature-drift-pins.json'
CANONICAL='532234a73caefaadee0ef39a75108d9392b6de99e05fcbd763ce9634642c9077'
BASE='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
EXPECTED={'H19-balance-projection':11,'H19-balance-domain':1,'H60-typing-parameter':7,'removed-private-identity':3}
COVERAGE=ROOT/'tests/h62/item2/audit-readonly-calls/coverage.json'

def sha(raw):return hashlib.sha256(raw).hexdigest()
def pairs(items):
    out={}
    for k,v in items:
        if k in out:raise ValueError('duplicate JSON key')
        out[k]=v
    return out
def unique(rows):
    out={(r['file'],r['source_name']):r for r in rows}
    if len(out)!=len(rows):raise ValueError('duplicate original/pair identity')
    return out

def bind(frozen,pins,packet):
    originals=unique(frozen['declarations'])
    if frozen['base']!=BASE or len(originals)!=792:raise ValueError('original792 identity mismatch')
    expected=unique(pins['cases']);provided=unique(packet['pairs']+packet['private_identity_gaps'])
    if pins['original_base']!=BASE or Counter(p['kind'] for p in pins['cases'])!=EXPECTED or set(provided)!=set(expected):raise ValueError('exact19 pairs/3gaps required')
    if len(packet['pairs'])!=19 or len(packet['private_identity_gaps'])!=3 or any(r['kind']=='removed-private-identity' for r in packet['pairs']) or any(r['kind']!='removed-private-identity' for r in packet['private_identity_gaps']):raise ValueError('private/public case partition drift')
    if any(provided[k]['kind']!=v['kind'] for k,v in expected.items()):raise ValueError('pair kind substitution')
    if packet['transport_proofs_supplied']!=0 or packet['original_obligations_discharged']!=0:raise ValueError('producer proof credit forbidden')
    annotations={}
    for key,pin in expected.items():
        row=provided[key];old=originals.get(key);source=row['original']
        if old is None or source is None or any(source[k]!=old[k] for k in ['file','source_name','signature_sha256','variable_context','visibility']):raise ValueError('original lexical/type identity mismatch')
        if source['signature_sha256']!=pin['original_signature_sha256']:raise ValueError('consumer original pin mismatch')
        if row['transport_proof']!={'status':'not supplied','reference':None} or row['h57_authorization']!='not independently verified' or row['kernel_fidelity']!='pending; no Lean executed' or row['original_obligation_discharged'] is not False:raise ValueError('unproved transport promotion')
        missing=row['kind']=='removed-private-identity'
        if missing and (old['visibility']!='private' or row['current'] is not None):raise ValueError('removed private identity remapped')
        annotations[key]={'kind':row['kind'],'current':row['current'],'matches_recorded_source_observation':row['current_matches_recorded_observation'],
          'frozen_kernel_name':old['kernel_name'],'frozen_raw_type_sha256_reference':old['elaborated']['raw_type_sha256'],
          'frozen_kernel_reference_only':True,'current_kernel_type_checked':False,'transport_proof_supplied':False,
          'h57_authorization_verified':False,'original_credit_added':False,'private_identity_gap_retained':missing,
          'source_request_routing_lane':'solidity-v07-v11-20261030/v10-storage-operations','live_ownership_attested':False}
    rows=[{'frozen':r,'transport_source_intake':annotations.get((r['file'],r['source_name']))} for r in frozen['declarations']]
    return {'schema':1,'original_base':BASE,'original_obligations':792,'rows':rows,'linked_source_pairs':19,'private_gaps':3,
      'historical_statuses':dict(Counter(r['witness_status'] for r in frozen['declarations'])),
      'transport_proofs_supplied':0,'original_obligations_discharged':0,'current_kernel_fidelity':False,'runtime_gate_pass':False,'timing_stop_released':False}

def execute_published(buffers,head):
    """Compile the very buffers compared with Git, including the direct helper."""
    allowed={str(PRODUCER.resolve()),str(SCANNER.resolve())}
    for path in allowed:
        actual=subprocess.check_output(['git','show',head+':'+str(Path(path).relative_to(ROOT))],cwd=ROOT)
        if buffers[path]!=actual:raise ValueError('executed published tool differs from Git')
    original_factory=importlib.util.spec_from_file_location
    class CapturedLoader(importlib.machinery.SourceFileLoader):
        def get_code(self,fullname):return compile(buffers[self.path],self.path,'exec',dont_inherit=True)
    def factory(name,path,*args,**kwargs):
        path=str(Path(path).resolve())
        if path not in allowed:raise ValueError('unadmitted dynamic producer helper')
        return original_factory(name,path,loader=CapturedLoader(name,path))
    try:
        importlib.util.spec_from_file_location=factory
        spec=factory('executed_source_transport_producer',PRODUCER)
        producer=importlib.util.module_from_spec(spec);spec.loader.exec_module(producer)
        return producer
    finally:importlib.util.spec_from_file_location=original_factory

def run(ledger,output):
    output=output.resolve()
    if output.is_relative_to(ROOT):raise ValueError('bulk evidence must be outside checkout')
    source=ledger.read_bytes()
    if sha(source)!=CANONICAL:raise ValueError('unadmitted original ledger')
    frozen=json.loads(source,object_pairs_hook=pairs)
    # Seal the entire H62 Python tree before any producer/helper is imported.
    tool_buffers={str(p.resolve()):p.read_bytes() for scope in ['scripts/h62','tests/h62'] for p in (ROOT/scope).rglob('*.py')}
    protected={path:sha(raw) for path,raw in tool_buffers.items()}
    pin_raw=PINS.read_bytes();coverage=COVERAGE.read_bytes();protected[str(PINS)]=sha(pin_raw);protected[str(COVERAGE)]=sha(coverage);protected[str(ledger.resolve())]=CANONICAL
    pins=json.loads(pin_raw,object_pairs_hook=pairs)
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    output.mkdir(parents=True,exist_ok=False)
    producer=execute_published(tool_buffers,head)
    if sha(pin_raw)!=producer.PIN_SHA:raise ValueError('producer admission mismatch')
    code=producer.run(output/'producer');packet_path=output/'producer/pairs.json';packet_raw=packet_path.read_bytes();packet=json.loads(packet_raw,object_pairs_hook=pairs)
    protected[str(packet_path)]=sha(packet_raw)
    for path in [PRODUCER,SCANNER]:
        saved=output/'executed-tools'/path.relative_to(ROOT);saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(tool_buffers[str(path)])
        protected[str(saved)]=sha(tool_buffers[str(path)])
    if code!=0 or packet['current_head']!=head or packet['original_base']!=BASE or packet['consumer_pins_sha256']!=sha(pin_raw):raise ValueError('failed or substituted producer observation')
    if packet['generator_sha256']!=protected[str(PRODUCER)] or packet['scanner_sha256']!=protected[str(Path(producer.census.__file__))]:raise ValueError('producer/helper source substitution')
    wanted={(label,path) for label in ['original','current'] for path in {r['file'] for r in pins['cases']}}
    seen=set();source_pins={};source_buffers={}
    for row in packet['sources']:
        label='original' if row['revision']==BASE else 'current'
        key=(label,row['path'])
        if key not in wanted or key in seen or row['revision']!=(BASE if label=='original' else head):raise ValueError('captured source membership drift')
        path=(output/'producer'/row['artifact']).resolve()
        if not path.is_relative_to(output/'producer'):raise ValueError('captured source traversal')
        raw=path.read_bytes();actual=subprocess.check_output(['git','show',row['revision']+':'+row['path']],cwd=ROOT)
        if raw!=actual or sha(raw)!=row['sha256']:raise ValueError('captured source Git binding drift')
        if label=='current' and (ROOT/row['path']).read_bytes()!=raw:raise ValueError('current uncommitted source drift')
        source_pins[str(path)]=sha(raw);source_buffers[key]=raw;seen.add(key)
    if seen!=wanted:raise ValueError('missing captured source')
    result=bind(frozen,pins,packet)
    # Independently reparse captured rows and compare every actual signature/context.
    for row in packet['pairs']+packet['private_identity_gaps']:
        for label,field in [('original','original'),('current','current')]:
            raw=source_buffers[label,row['file']]
            parsed=unique(producer.census.declarations_text(row['file'],raw.decode()))
            if parsed.get((row['file'],row['source_name']))!=row[field]:raise ValueError('source pair does not match captured declarations')
    outputs={'obligations.json':(json.dumps(result,ensure_ascii=False,indent=2)+'\n').encode(),'original-ledger.json':source}
    for name,raw in outputs.items():
        (output/name).write_bytes(raw);protected[str(output/name)]=sha(raw)
    for path,pin in (protected|source_pins).items():
        if sha(Path(path).read_bytes())!=pin:raise ValueError('input/tool/source drift during intake')
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()!=head:raise ValueError('head changed during intake')
    receipt={'schema':1,'status':'pass','source_head':head,'producer_file':str(PRODUCER.relative_to(ROOT)),
      'producer_file_git_commit':subprocess.check_output(['git','log','-1','--format=%H','--',str(PRODUCER.relative_to(ROOT))],cwd=ROOT,text=True).strip(),
      'producer_packet_sha256':sha(packet_raw),'canonical_sha256':CANONICAL,'protected_sha256':protected|source_pins,
      'output_sha256':{name:sha(raw) for name,raw in outputs.items()},'producer_and_helper_execution':'retained buffers equal to exact Git HEAD blobs',
      'linked_source_pairs':19,'private_gaps':3,'original_obligations':792,'ordinary_pending':result['historical_statuses']['pending'],
      'original_credit_added':0,'source_pair_delivery':'received and Git/source-bound','kernel_types_transports_and_h57':'not supplied or verified',
      'historical_recorded_commit_available':packet['recorded_observed_head_available'],'runtime_gate_pass':False,'timing_stop_released':False}
    (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');return receipt
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--original-ledger',type=Path,required=True);parser.add_argument('--output',type=Path,required=True);a=parser.parse_args()
    print(json.dumps({k:v for k,v in run(a.original_ledger,a.output).items() if k not in ['protected_sha256','output_sha256']}))
