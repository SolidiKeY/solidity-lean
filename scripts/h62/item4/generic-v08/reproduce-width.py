#!/usr/bin/env python3
"""Rebuild isolated admission backfill, never the blocked semantic family gates."""
import argparse,fcntl,hashlib,json,os,pathlib,re,subprocess,sys
from census import ROOT,mask
p=argparse.ArgumentParser(__doc__)
p.add_argument('--toolchain',type=pathlib.Path,required=True)
p.add_argument('--archive',type=pathlib.Path,required=True)
p.add_argument('--output',type=pathlib.Path,required=True)
a=p.parse_args()
a.output=a.output.resolve()
if a.output==ROOT or ROOT in a.output.parents:p.error('bulk artifacts must be outside git')
if hashlib.file_digest(a.archive.open('rb'),'sha256').hexdigest()!='7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d':
    p.error('archive does not match coordinator pin')
lean=str((a.toolchain/'bin/lean').resolve())
version=subprocess.check_output([lean,'--version'],text=True)
if 'version 4.35.0,' not in version or 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' not in version:
    p.error('installed toolchain does not match coordinator pin')
a.output.mkdir(parents=True,exist_ok=True)
(a.output/'version.txt').write_text(version)
lockpath=pathlib.Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock')
lockpath.parent.mkdir(parents=True,exist_ok=True)
with lockpath.open('a') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    (a.output/'status.txt').write_text(subprocess.check_output(['git','status','--short'],cwd=ROOT,text=True))
    seen=set();order=[]
    def visit(module):
        path=ROOT/(module.replace('.','/')+'.lean')
        if module in seen or not path.exists():return
        seen.add(module)
        for dep in re.findall(r'^import (\S+)',mask(path.read_text()),re.M):visit(dep)
        order.append(module)
    visit('Solidity.Source.Types')
    env=dict(os.environ,LEAN_PATH=str(a.output/'lib'),LEAN_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
    commands=[]
    for module in order:
        file=module.replace('.','/')+'.lean'
        target=a.output/'lib'/(module.replace('.','/')+'.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        commands.append((module,[lean,'-j1','--tstack=131072','-o',str(target),file]))
    commands.append(('IntrinsicWidths',[lean,'-j1','--tstack=131072','tests/h62/item4/generic-v08/IntrinsicWidths.lean']))
    for name,command in commands:
        run=[sys.executable,str(ROOT/'scripts/h62/item4/generic-v08/bounded.py'),'--record',str(a.output/f'{name}.json'),'--']+command
        with (a.output/f'{name}.log').open('w') as log:
            result=subprocess.run(run,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
        print(name,result.returncode,flush=True)
        if result.returncode:sys.exit(result.returncode)
print('PASS isolated admission backfill only; no family RUNTIME_GATE_PASS')
