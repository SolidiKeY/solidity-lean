#!/usr/bin/env python3
"""Guard producer source publication being mistaken for kernel/compiler acceptance.
Capture exact Git blobs and candidate theorem header spans, preserving complete
lexical parser refusals. No original792 credit, ownership transfer, complete
namespace/signature binding, Lean execution or runtime acceptance is inferred.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('intake_initialization_gate',Path(__file__).with_name('check_initialization.py'))
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
FILES=['Solidity/Backend/AbiWorld/PublicCompilerTotal.lean','Solidity/Backend/AbiWorld/PublicCompilerTotalControls.lean','Solidity/Backend/AbiWorld/P1RevertBridge.lean','Solidity/Evm/Compiler.lean','docs/feature-work/v13-public-compiler-total.md']
PREFIX='Solidity.Backend.AbiWorld.PublicCompilerTotal.'
CONTROLS='Solidity.Backend.AbiWorld.PublicCompilerTotalControls.'
REQUESTED=[PREFIX+x for x in ['compile_core','compile_isSome','compile_init','compile_agrees']]+[CONTROLS+x for x in ['program_ok','program_accepted','program_kernel','program_code_nonempty','program_agrees_fresh']]

def candidate_header(raw,name):
    text=raw.decode();short=name.rsplit('.',1)[-1]
    hits=list(re.finditer(r'(?m)^theorem '+re.escape(short)+r'(?![\w\'])',text))
    if len(hits)!=1:raise ValueError('missing/duplicate requested header span')
    start=hits[0].start();end=text.find(':=',start)
    if end<0:raise ValueError('missing header delimiter')
    header=text[start:end].encode()
    return {'requested_name':name,'status':'candidate-header-only-namespace-and-kernel-binding-pending',
            'byte_start':len(text[:start].encode()),'byte_end':len(text[:end].encode()),
            'header_span':header.decode(),'header_span_sha256':hashlib.sha256(header).hexdigest()}

def surface_rows(rows):
    # The frozen-corpus census supplies assignment-specific ownership/witness
    # defaults. They have no authority for these newly published files.
    keys=['file','line','signature','signature_sha256','variable_context','visibility']
    return [dict({k:row[k] for k in keys},candidate_source_name=row['source_name'],
                 binding_status='lexical-only-kernel-and-live-owner-unverified') for row in rows]

def run(head,output):
    if not re.fullmatch('[0-9a-f]{40}',head):raise ValueError('exact commit required')
    def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
    merge=git('rev-parse','546dadda3').decode().strip()
    subprocess.run(['git','merge-base','--is-ancestor',merge,head],cwd=ROOT,check=True)
    output.mkdir(parents=True,exist_ok=False);records=[];buffers={}
    for path in FILES:
        raw=git('show',head+':'+path);buffers[path]=raw
        saved=output/path;saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(raw)
        record={'file':path,'git_blob':git('rev-parse',head+':'+path).decode().strip(),'sha256':hashlib.sha256(raw).hexdigest()}
        if path.endswith('.lean'):
            try:
                rows=gate.original.export.census.declarations_text(path,raw.decode())
                record.update(lexical_status='parsed-lexical-only',lexical_declarations=surface_rows(rows))
            except ValueError as exc:
                record.update(lexical_status='refused-no-complete-declaration-binding',refusal=str(exc),lexical_declarations=[])
        records.append(record)
    candidates=[]
    for name in REQUESTED:
        path=FILES[1] if name.startswith(CONTROLS) else FILES[0]
        candidate=candidate_header(buffers[path],name);candidate['file']=path;candidates.append(candidate)
    for path,raw in buffers.items():
        if git('show',head+':'+path)!=raw or (output/path).read_bytes()!=raw:raise ValueError('Git source capture drift')
    receipt={'schema':1,'status':'published-source-only-not-consumer-kernel-accepted','head':head,'source_scope':'exact Git snapshot; no current-tree or complete namespace claim','producer_merge':merge,'files':records,'requested_headers':candidates,
      'compiler_entry':'Solidity.Evm.Compiler.compile','success_domain':'Owner-stated ProgOk K P and Matches K F; fresh entry uses ProgOk [] P. No audit weakening.',
      'observation':'Compilation.Agrees one-direction disjunction; data-free machine revert, guarded panic/payment/divergence cases.',
      'publication_wait':'Source publication delivered; consumer kernel acceptance and complete negative controls pending.',
      'remaining':{'library_body_binding':'G42.04 remains explicit owner duty; totality domain excludes external/self/library calls.','gas_depth_fork':'Owner P1 documentation explicitly says gas/depth are not resources; no gas/fork result credited.','H121_source_native_frame':'Our own full producer unfinished.','lexical_namespace_binding':'Refused files remain unbound; candidate spans are not exact kernel signatures.'},
      'original_obligations_discharged':0,'compiler_success_kernel_validation':False,'runtime_gate_pass':False,
      'boundary':'Git/source/header-span inventory only. No Lean execution of producer modules in this milestone; owner test reports are not consumer gate evidence.'}
    (output/'receipt.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
    return receipt

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--head',required=True);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    with gate.current.headers.binder.writer_lease():receipt=run(args.head,args.output)
    print(json.dumps({'status':receipt['status'],'requested_headers':len(receipt['requested_headers']),'refused_files':[x['file'] for x in receipt['files'] if x.get('lexical_status','').startswith('refused')],'original_credit':0}))
if __name__=='__main__':main()
