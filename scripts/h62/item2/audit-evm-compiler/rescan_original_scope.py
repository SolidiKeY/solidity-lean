#!/usr/bin/env python3
"""Reproduce only the original frozen census after additive map integration.
The existing full-map census gate remains unchanged and may fail separately.
"""
import argparse,difflib,json,pathlib,re,subprocess
import census as scanner
ROOT=pathlib.Path(__file__).resolve().parents[4]
BASE='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
def validate_additive_map(original,current):
    old_lines=original.splitlines();new_lines=current.splitlines();extra=[]
    for tag,_,_,start,end in difflib.SequenceMatcher(None,old_lines,new_lines,autojunk=False).get_opcodes():
        if tag=='equal':continue
        if tag!='insert':raise ValueError('original map lines removed or modified')
        inserted=new_lines[start:end]
        if any(not re.fullmatch(r'\| `[^`]+\.lean` \| .* \|',line) for line in inserted):raise ValueError('non-module map change')
        extra.extend(inserted)
    paths=re.findall(r'^\| `([^`]+\.lean)`',current,re.M)
    if len(paths)!=len(set(paths)):raise ValueError('duplicate current module path')
    return extra

def main():
    p=argparse.ArgumentParser();p.add_argument('--frozen-census',required=True);p.add_argument('--output',required=True);p.add_argument('--verification',required=True);a=p.parse_args()
    subprocess.run(['git','merge-base','--is-ancestor',BASE,'HEAD'],cwd=ROOT,check=True)
    show=lambda name:subprocess.check_output(['git','show',BASE+':'+name],cwd=ROOT)
    map_text=show('docs/module-map/evm-compiler.md').decode()
    modules=re.findall(r'^\| `([^`]+\.lean)`',map_text,re.M)
    if len(modules)!=len(set(modules)):raise ValueError('duplicate original module')
    frozen=json.loads(pathlib.Path(a.frozen_census).read_text())
    if frozen['base']!=BASE or frozen['modules']!=modules or frozen['module_map_sha256']!=scanner.sha(map_text):raise ValueError('original scope mismatch')
    records=[];tokens=0
    for module in modules:
     relative=module if module.startswith('Bridge/') else 'Solidity/'+module;path=ROOT/relative
     if path.read_bytes()!=show(relative):raise ValueError('frozen source changed: '+relative)
     text=path.read_text();tokens+=len(re.findall(r'\btheorem\s',scanner.mask(text)))
     for row in scanner.scan(path):
      row.update(file=relative,module_map_area='evm-compiler',source_file_sha256=scanner.sha(text),owner_status='pending-producer-reconciliation');records.append(row)
    if tokens!=len(records):raise ValueError('theorem token mismatch')
    result=dict(schema=2,signature_parser='balanced-root-let-match-aware',base=BASE,module_map_sha256=scanner.sha(map_text),modules=modules,module_count=len(modules),candidate_count=len(records),kernel_verified=False,statements=records)
    if result!=frozen:raise ValueError('regenerated frozen census differs')
    current=(ROOT/'docs/module-map/evm-compiler.md').read_text()
    extra=validate_additive_map(map_text,current)
    pathlib.Path(a.output).write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    verification=dict(base=BASE,original_modules=len(modules),original_declarations=len(records),original_sources_byte_identical=True,current_map_byte_identical=current==map_text,additive_unassigned_map_rows=extra,full_map_gate='separate; not waived',scope='original frozen modules only')
    pathlib.Path(a.verification).write_text(json.dumps(verification,indent=2)+'\n');print(json.dumps(dict(original_modules=len(modules),original_declarations=len(records),unassigned_additions=len(extra))))

if __name__=='__main__':main()
