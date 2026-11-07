#!/usr/bin/env python3
"""Source-bound successor acceptance. Data samples, joint premises and closed fidelity stay distinct."""
import argparse,hashlib,json,pathlib,re,subprocess,sys
from census import ROOT,census
from inventory import split_declaration,source_context

TOOL=pathlib.Path('/workspace/.setup/tools/lean-4.24.0-linux/bin')
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def tool_identity():
 assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.24.0'
 result={}
 for name,version in [('lean','Lean (version 4.24.0'),('lake','Lake version 5.0.0-src+797c613')]:
  binary=TOOL/name;text=subprocess.check_output([str(binary),'--version'],text=True).strip();assert text.startswith(version)
  result[name]=dict(path=str(binary),sha256=sha(binary),version=text)
 assert '797c613eb9b6d4ec95db23e3e00af9ac6657f24b' in result['lean']['version']
 return result
TOOLS=tool_identity()
def core_inputs(proof):
 found={}
 def visit(p):
  p=p.resolve()
  if str(p) in found:return
  found[str(p)]=sha(p)
  for line in p.read_text().splitlines():
   if line.startswith('import '):
    imports=[n for n in line.split()[1:] if n.startswith('Solidity.')]
    assert len(imports)<=1,'legacy recorder requires one core import per line'
    for n in imports:visit(ROOT/(n.replace('.','/')+'.lean'))
 visit(proof);return found

def frozen_inputs():
 pins=json.loads((ROOT/'Bridge/tests/precompile-agreement/inventory.json').read_text())['pins'];assert len(pins)==75
 assert all(sha(ROOT/p)==h for p,h in pins.items())
 expected={str(ROOT/p):h for p,h in pins.items()}
 for f in census()['files']:expected[str(ROOT/f['path'])]=f['source_sha256']
 assert len(expected)==81;return expected

def valid_receipt(e,stem,proof,cwd):
 import os
 m=json.loads((e/(stem+'.json')).read_text());logpath=e/(stem+'.log');log=logpath.read_text()
 required={'exit','timeout','resource_stop','inputs_unchanged','cwd','lean_num_threads','swap','command','toolchain','address_space_cap_bytes','reserve_bytes','aggregate_peak_rss_bytes','minimum_available_bytes','wall_seconds','input_sha256','log_sha256'}
 assert required<=m.keys(),'incomplete receipt'
 assert m['exit']==0 and not m['timeout'] and not m['resource_stop'] and m['inputs_unchanged']
 assert m['cwd']==str(cwd) and m['lean_num_threads']==1 and m['swap']=='disabled'
 expected=[str(TOOL/'lake'),'env','lean','-j1','-M11264','--tstack=131072',os.path.relpath(proof,cwd)]
 assert m['command']==expected,'not the exact pinned elaboration command'
 assert m['toolchain']==TOOLS,'tool identity differs'
 assert m['address_space_cap_bytes']==12*1024**3 and m['reserve_bytes']==4*1024**3
 assert 0<=m['aggregate_peak_rss_bytes']<=12*1024**3 and m['minimum_available_bytes']>=4*1024**3
 assert 0<m['wall_seconds']<=300
 assert m['input_sha256']==core_inputs(proof),'source closure differs'
 assert m['log_sha256']==sha(logpath),'unbound or modified log'
 assert 'sorryAx' not in log and ': error:' not in log
 for axes in re.findall(r"'[^']+' depends on axioms: \[([^\]]*)\]",log,re.S):
  assert {a.strip() for a in axes.split(',') if a.strip()}<=set(['propext','Classical.choice','Quot.sound']),'nonstandard printed axiom'
 if cwd==ROOT/'Bridge':
  assert 'frozen_input_sha256' in m and 'frozen_inputs_unchanged' in m,'missing frozen closure'
  assert m['frozen_inputs_unchanged'] and m['frozen_input_sha256']==frozen_inputs(),'frozen closure differs'
 if stem=='identity-final424':assert 'IDENTITY_APPLICABILITY_PASS joint=6 data=4 guards=13 controls=3' in log
 return m,log

def generate(e):
 c=census();d=ROOT/'tests/h62/item2/audit-precompiles'
 for script in ['generate_identity.py','generate_bridge_fidelity.py','generate_bytes_gas.py','generate_header.py','generate_bls.py','generate_remaining_fidelity.py','fidelity.py']:
  subprocess.run([sys.executable,str(ROOT/'scripts/h62/item2/audit-precompiles'/script),'--check'],check=True,stdout=subprocess.DEVNULL)
 subprocess.run([sys.executable,str(ROOT/'scripts/h62/item2/audit-precompiles/coverage.py'),'--evidence',str(e)],check=True,stdout=subprocess.DEVNULL)
 base=json.loads((e/'statement-coverage.json').read_text());assert len(base['rows'])==138 and base['applicability_checked']==24
 baseline={r['name']:r for r in base['rows'] if r['status']!='pending'};assert len(baseline)==24
 for stem,src in [('basic-final','BasicWitnesses'),('core-final','CoreWitnesses'),('data-final','DataWitnesses'),('type-fidelity-final','TypeFidelity')]:valid_receipt(e,stem,d/(src+'.lean'),ROOT)
 for stem,src,ns,n,guards in [('osaka-ledger-final424','OsakaWitnesses','Osaka',5,5),('bls-ledger-final424','BlsWitnesses','Bls',18,20),('point-ledger-final424','PointEvalWitnesses','PointEval',5,5),('stipend-ledger424','StipendWitnesses','Stipend',12,12)]:
  _,log=valid_receipt(e,stem,d/(src+'.lean'),ROOT)
  assert 'CORE_APPLICABILITY_PASS module='+ns+' original='+str(n)+' guards='+str(guards) in log
  assert (d/(src+'.lean')).read_text().count('#guard_msgs in')==guards
 _,successlog=valid_receipt(e,'point-success-final424',d/'PointEvalSuccess.lean',ROOT)
 assert 'H62.AuditPrecompiles.Successor.PointEvalSuccess.pointEval_result_joint :' in successlog
 assert (d/'PointEvalSuccess.lean').read_text().count('#guard_msgs in')==11
 _,remaininglog=valid_receipt(e,'remaining-fidelity-final424',d/'RemainingCoreFidelity.lean',ROOT)
 assert 'REMAINING_CORE_FULL_TYPE_FIDELITY_PASS total=41' in remaininglog
 identity,il=valid_receipt(e,'identity-final424',d/'BridgeIdentityWitnesses.lean',ROOT/'Bridge')
 bg,bgl=valid_receipt(e,'bytes-gas-final424',d/'BridgeBytesGasWitnesses.lean',ROOT/'Bridge')
 hd,hdl=valid_receipt(e,'header-short-zero424',d/'BridgeHeaderWitnesses.lean',ROOT/'Bridge')
 assert 'HEADER_APPLICABILITY_PASS joint=10 data=7' in hdl
 hdpins=json.loads((d/'header-pins.json').read_text());assert len(hdpins)==17 and all(set(a)<=set(['propext','Classical.choice','Quot.sound']) for a in hdpins.values())
 assert (d/'BridgeHeaderWitnesses.lean').read_text().count('#guard_msgs in')==17
 assert 'BYTES_GAS_APPLICABILITY_PASS joint=2 data=19 guards=22' in bgl
 bgpins=json.loads((d/'bytes-gas-pins.json').read_text());assert len(bgpins)==22 and all(set(a)<=set(['propext','Classical.choice','Quot.sound']) for a in bgpins.values())
 assert (d/'BridgeBytesGasWitnesses.lean').read_text().count('#guard_msgs in')==22
 fidelity,fl=valid_receipt(e,'bridge-fidelity-final424',d/'BridgeFidelity.lean',ROOT/'Bridge')
 valid_receipt(e,'stipend-control424',d/'StipendControl.lean',ROOT)
 valid_receipt(e,'keysort424',ROOT/'Solidity/KeySort.lean',ROOT)
 _,axlog=valid_receipt(e,'imported-bridge-axioms424',ROOT/'Bridge/tests/precompile-agreement/AllDeclarations.lean',ROOT/'Bridge')
 assert 'ALL_DECLARATIONS_PASS count=204' in axlog
 assert 'BRIDGE_FULL_TYPE_FIDELITY_PASS total=73 private=4 closed=25' in fl
 private=dict(re.findall(r'^PRIVATE_CONSTANT ([^:]+): (.+)$',fl,re.M));assert len(private)==4
 pins=json.loads((d/'successor-identity-pins.json').read_text());assert len(pins)==13 and all(set(a)<=set(['propext','Classical.choice','Quot.sound']) for a in pins.values())
 proof=(d/'BridgeIdentityWitnesses.lean').read_text();assert proof.count('#guard_msgs in')==13
 core={f['path'] for f in c['files'] if f['path'].split('/')[-1] in ['Field.lean','Basic.lean','Modexp.lean','Bn254.lean','Blake2f.lean','P256.lean'] and f['path'].startswith('Solidity/')}
 joint={'identity_success','identity_failure','identity_charged','identity_exact','identity_one_short','identity_unaffordable'}
 rows=[]
 for f in c['files']:
  for old in f['declarations']:
   name=old['name'];bs,goal=split_declaration(old);bridge=f['path'].startswith('Bridge/')
   if bridge:assert not source_context((ROOT/f['path']).read_text(),old['line'])
   row=dict(name=name,file=f['path'],signature_sha256=old['signature_sha256'],full_type_fidelity=True,joint_witness=False,data_domain_sample=False,closed_fidelity=bridge and not bool(bs),witness=None,target='frozen Lean4.24.0; not migrationv4.35')
   if name in baseline:
    b=baseline[name];row.update(joint_witness=b['status']=='witness-checked',data_domain_sample=b['status']=='data-input-checked',witness=b['witness'])
   if f['path']=='Bridge/SolidityBridge/PrecompileAgreement/Identity.lean':
    short=name.split('.')[-1];kind='joint' if short in joint else 'data';row.update(joint_witness=kind=='joint',data_domain_sample=kind=='data',witness='H62.AuditPrecompiles.Successor.'+short+'_'+kind)
   if f['path'] in ['Bridge/SolidityBridge/PrecompileAgreement/Bytes.lean','Bridge/SolidityBridge/PrecompileAgreement/Gas.lean'] and name.split('.')[-1]!='address_table':
    short=name.split('.')[-1];kind='joint' if short in ['ofNat_nat','subtract_nat'] else 'data';row.update(joint_witness=kind=='joint',data_domain_sample=kind=='data',witness='H62.AuditPrecompiles.Successor.BytesGas.'+short+'_'+kind)
   if f['path']=='Bridge/SolidityBridge/PrecompileAgreement/Header.lean' or name=='SolidityBridge.PrecompileAgreement.Controls.blake_malformed_lengths':
    short=name.split('.')[-1];kind='joint' if short in ['blake_zero_header','blake_price','blake_gas','blake_valid','blake_insufficient','blake_invalid_flag','blake_valid_one','blake_invalid_size','blake_zero_gas','blake_malformed_lengths'] else 'data';row.update(joint_witness=kind=='joint',data_domain_sample=kind=='data',witness='H62.AuditPrecompiles.Successor.Header.'+short+'_'+kind)
   short=name.split('.')[-1];kind=wn=None
   if f['path']=='Solidity/Precompiles/Osaka.lean':
    kind,wn={'fixed_precompileGas':('closed','fixed_gas_fidelity'),'run_eq_none_iff':('data','run_failure_data'),'fixed_precompile_eq_none_iff':('data','fixed_failure_data'),'gas_mono':('joint','gas_mono_joint'),'ecrecover_exceeds_stipend':('data','ecrecover_stipend_data')}[short];ns='Osaka'
   if f['path']=='Solidity/Precompiles/Bls12381.lean':
    kind='closed' if short in ['g1Discount_length','g2Discount_length'] else 'joint' if short in ['msmGas_succ','msmGas_mono','g1MsmGas_mono','g2MsmGas_mono','pairingGas_mono'] else 'data'
    wn=short+('_fidelity' if kind=='closed' else '_'+kind);ns='Bls'
   if f['path']=='Solidity/Precompiles/PointEval.lean' and short!='pointEval_result':
    kind,wn={'bind_check_eq_none':('data','bind_failure_data'),'bind_check_eq_some':('joint','bind_success_joint'),'pointEval_eq_none_iff':('data','failure_data'),'decode_length':('joint','decode_length_joint'),'pointEval_length':('joint','pointEval_length_joint')}[short];ns='PointEval'
   if name=='Solidity.Precompiles.PointEval.pointEval_result':
    kind='joint';wn='pointEval_result_joint';ns='PointEvalSuccess'
   if f['path']=='Solidity/Stipend/Rule.lean':
    kind='joint' if short in ['not_fits_cons','pow_not_fits'] else 'data';wn=short+'_'+kind;ns='Stipend'
   if kind:row.update(joint_witness=kind=='joint',data_domain_sample=kind=='data',closed_fidelity=kind=='closed',witness='H62.AuditPrecompiles.Successor.'+ns+'.'+wn)
   assert sum(bool(row[k]) for k in ['joint_witness','data_domain_sample','closed_fidelity'])<=1,'multiple accounting roles'
   if old['visibility']=='private':assert name in private;row['actual_private_constant']=private[name]
   row['case_accounted']=row['joint_witness'] or row['data_domain_sample'] or row['closed_fidelity'];rows.append(row)
 assert len(rows)==len({x['name'] for x in rows})==138
 counts={k:sum(bool(x[k]) for x in rows) for k in ['full_type_fidelity','joint_witness','data_domain_sample','closed_fidelity','case_accounted']}
 assert counts==dict(full_type_fidelity=138,joint_witness=37,data_domain_sample=73,closed_fidelity=28,case_accounted=138),counts
 return dict(schema_version=1,status='partial',target='frozen v4.24; no v4.35 acceptance',statements=138,counts=counts,pending=0,owner_compiler_success_supplied=False,rows=rows,identity_seconds=identity['wall_seconds'],fidelity_seconds=fidelity['wall_seconds'],bytes_gas_seconds=bg['wall_seconds'],header_seconds=hd['wall_seconds'],boundaries=['Closed fidelity is not a fabricated exists-True witness.','Six IDENTITY proof-premise cases construct the same data and hypothesis together.','Astronomical-array witness is symbolic model inhabitance, not practical allocation.','RejectAll negative control is a precompile flag function, not an actual compiler theorem.','H85/H86 host build wrapper/allow-rule verification and migration435/owner success obligations remain.'])

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--evidence',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args();v=generate(a.evidence);s=json.dumps(v,indent=2)+'\n';dest=a.evidence/'successor-coverage.json'
 if a.check:assert dest.read_text()==s
 else:dest.write_text(s)
 print('SUCCESSOR_PARTIAL statements138 full_types138 joint37 data73 closed28 accounted138 pending0; no compiler-success/full-gate claim')
