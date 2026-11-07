#!/usr/bin/env python3
"""Refresh local registrations/report, or pin exact messages from a passed report.
This performs accounting generation only; run the independent kernel gate next.
"""
import fcntl,hashlib,json,pathlib,re,sys
here=pathlib.Path(__file__).resolve().parent
root=here.parents[2]
folder=root/'tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28'
def save(p,v): p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
files=sorted(folder.glob('*.lean'))
imports=''.join('import '+'Solidity.Assurance.NonVacuityH28.'+p.stem+'\n' for p in files if p.stem not in ['Pins','Signatures'])
if len(sys.argv)==1:
 old=json.loads((here/'signature-names.json').read_text())
 names=[n for n in old if not n.startswith('Solidity.Assurance.NonVacuityH28.')]
 names=list(dict.fromkeys(names+[x['id'] for x in json.loads((here/'public-contracts.json').read_text())['contracts']]))
 names+=['Solidity.Assurance.NonVacuityH28.'+n for p in files for n in re.findall(r"^theorem ([\w']+)",p.read_text(),re.M)]
 assert len(names)==len(set(names))
 save(here/'signature-names.json',names)
 save(here/'registration.json',{'modules':[{'module':'Solidity.Assurance.NonVacuityH28.'+p.stem,'file':str(p.relative_to(root)),'description':p.stem+' H28 local evidence'} for p in files], 'central_registration':'deferred to integrator by exclusive-scope assignment'})
 (folder/'Signatures.lean').write_text(imports+'\n/-! Exact kernel signatures and measured axiom sets; no semantic witness. -/\nset_option pp.explicit true\nset_option pp.universes true\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names))
 print('report generated:',len(names),'names')
else:
 log=here/sys.argv[1]; meta=json.loads(log.with_suffix('.json').read_text()); assert meta['exit']==0 and meta['stop'] is None
 assert meta['log_sha256']==hashlib.sha256(log.read_bytes()).hexdigest(), 'measurement log hash differs'
 assert meta['input_sha256']['tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/Signatures.lean']==hashlib.sha256((folder/'Signatures.lean').read_bytes()).hexdigest(), 'report source hash differs'
 for path,digest in meta['input_sha256'].items():
  assert (root/path).is_file() and hashlib.sha256((root/path).read_bytes()).hexdigest()==digest, 'measured dependency/source differs: '+path
 text=log.read_text(); names=json.loads((here/'signature-names.json').read_text()); pins={}; guards=[]
 for n in names:
  pat="'"+re.escape(n)+r"' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)"
  matches=list(re.finditer(pat,text)); assert len(matches)==1,(n,len(matches))
  msg=matches[0].group(); axioms=re.search(r'\[([^\]]*)\]',msg)
  pins[n]=[a.strip() for a in axioms[1].split(',') if a.strip()] if axioms else []
  assert set(pins[n])<= {'propext','Classical.choice','Quot.sound'},(n,pins[n])
  guards.append('/-- info: '+msg+' -/\n#guard_msgs in #print axioms '+n+'\n')
 (folder/'Pins.lean').write_text(imports+'\n/-! Exact measured axiom pins. Changed sets fail the kernel gate. -/\n\n'+'\n'.join(guards))
 save(here/'axiom-pins.json',{'theorems':pins,'measurement_log':str(log.relative_to(here)),'measurement_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'status':'guard kernel check pending'})
 print('pins generated:',len(pins))
