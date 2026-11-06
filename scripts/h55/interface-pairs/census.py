#!/usr/bin/env python3
"""Read-only syntactic census and lease-boundary check, with off-git evidence."""
import fcntl, hashlib, json, pathlib, re, subprocess
ROOT=pathlib.Path(__file__).resolve().parents[3]
BASE='4d3790eadb8a5212233bc7d5e345817476b2f590'
OUT=pathlib.Path('/workspace/scratch/h55-interface-pairs/evidence')
SYMBOLS=('FrameCertificate','CompilerPremise','RuntimeConsumer','StorageWordCertificate',
         'BoundaryLink','MappedBoundaryLink','FixedPathRoom','MemoryPathRoom')
INPUTS=[
 'Solidity/Backend/MemoryCopies/'+x+'.lean'
 for x in ('Interface','InterfaceV2','InterfaceV2Laws','InterfaceV2Roots')
]+[
 'Solidity/Backend/Selection/'+x+'.lean'
 for x in ('Interface','InterfaceV2','InterfaceV2Controls','Premises','PremisesV2')
]+[
 'Solidity/Backend/Passes/Sequence.lean',
 'Solidity/Backend/Passes/MappedSequence.lean',
 'Solidity/Backend/MemoryCopies/FixedPathCopyInterface.lean',
 'Solidity/Backend/MemoryCopies/MemoryPathCopyInterface.lean']
def git(*args):
 return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def sha(data):return hashlib.sha256(data).hexdigest()
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
subprocess.run(['git','merge-base','--is-ancestor',BASE,'HEAD'],cwd=ROOT,check=True)
changed=git('diff','--name-only',BASE,'--').splitlines()
changed += git('ls-files','--others','--exclude-standard').splitlines()
allowed=('tests/h55/interface-pairs/','scripts/h55/interface-pairs/')
assert all(p.startswith(allowed) or p=='docs/feature-work/h55-interface-pairs.md' for p in changed),changed
inputs={}
for name in INPUTS:
 current=(ROOT/name).read_bytes()
 published=subprocess.check_output(['git','show',BASE+':'+name],cwd=ROOT)
 assert current==published,'migration input changed without transferred lease: '+name
 inputs[name]=sha(current)
args=['rg','-n','-w']
for symbol in SYMBOLS:args+=['-e',symbol]
result=subprocess.run(args+['Solidity'],cwd=ROOT,text=True,capture_output=True,check=True)
mentions={symbol:[] for symbol in SYMBOLS}
definitions={symbol:[] for symbol in SYMBOLS}
consumers={}
for line in result.stdout.splitlines():
 name,number,source=line.split(':',2)
 consumers[name]=sha((ROOT/name).read_bytes())
 for symbol in SYMBOLS:
  if re.search(r'\b'+symbol+r'\b',source):
   mentions[symbol].append(dict(path=name,line=int(number),source=source))
  if re.match(r'(?:structure|def|abbrev) '+symbol+r'\b',source):
   definitions[symbol].append(dict(path=name,line=int(number)))
data=dict(base=BASE,head=git('rev-parse','HEAD'),production_migrations=False,
 lease_dependency=dict(kind='CoordinatorLeaseNotice',state='pending',required_fields=[
 'actual current owner','accepted handoff','exact transferred existing paths']),
 input_sha256=inputs,consumer_sha256=consumers,definitions=definitions,mentions=mentions,
 limitations='Token mentions include comments; this census is not Lean reference resolution or a proof gate.')
OUT.mkdir(parents=True,exist_ok=True)
(OUT/'census.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({s:dict(definitions=definitions[s],files=len({x['path'] for x in mentions[s]}),
 mentions=len(mentions[s])) for s in SYMBOLS},indent=2))
print('H55_CENSUS_AND_UNCHANGED_INPUTS_PASS')
