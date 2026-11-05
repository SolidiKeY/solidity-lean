#!/usr/bin/env python3
"""Paired exact-source catalogue certificates; no Lean/Docker execution."""
import copy,hashlib,json,pathlib,re,runpy,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parent.parent
BASE='bad1d76aa094e8df9e7924273ba118a34325b8d8'
PUBLIC='24149fd567ec273e5c72760ecf0a25a940c4c4fc'
CONFIG={
 'Solidity/Lowering/V08/WorldImageAccess.lean':('Solidity.Lowering.V08.WorldImageAccess.','/-! Converse catalogue facts concern the initial image and actual typed lookup,','lookup_reflect lookup_some_iff lookup_none_iff lookup_none_of_code_absent lookup_none_of_kind_mismatch'.split()),
 'Solidity/Lowering/V08/WorldImageAccessControls.lean':('Solidity.Lowering.V08.CatalogueReflectionControls.','namespace Solidity.Lowering.V08.CatalogueReflectionControls','reflected_before reflected_after_reset actual_source_probes absent_code_not_absent_funds complete_observations wrong_code stale_transient_relation image actual_wrong_kind actual_reset_probe code_present_wrong_kind no_extra_installation two_kind_observations'.split())}
RUNNER=runpy.run_path(str(ROOT/'scripts/v08-image-access-run.py'),run_name='pure_helpers')
def sha(b):return hashlib.sha256(b).hexdigest()
def validate(file,source,before,result,log,bindings,raw):
 assert file in CONFIG
 for path in CONFIG:
  data=source if path==file else (ROOT/path).read_bytes()
  assert before['source'][path]==sha(data),'paired source binding'
 assert result['exit']==result['actual_exit']==0 and result['source_and_controls_checked'] and result['cleanup_stopped'] and result['H1']
 assert result['minimum_free_ram']>=4294967296 and result['peak_aggregate_rss']<=12884901888
 assert result['log_sha256']==bindings['decoded_sha256']==sha(log)
 assert bindings['raw_sha256']==sha(raw) and RUNNER['demux'](raw)==log
 assert b'H1_TARGET=@shared-file' in log and b'Build completed successfully (2 jobs).' in log and b'error:' not in log
 key='/workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/coord-access/current-file.txt'
 assert before['controls'][key]==sha((str(ROOT/file)+'\n').encode()),'exact checked file'
 for path in ['scripts/v08-coord-file.py','scripts/v08-coord-file-run.py','scripts/v08-integrated-check.sh','scripts/v08-published-bindings.json']:
  assert before['controls'][str(ROOT/path)]==sha((ROOT/path).read_bytes())
 assert before['peer']==RUNNER['verify_peer']() and before['peer']['published_head']==PUBLIC
 ns,marker,names=CONFIG[file];text=source.decode();prefix=text.split(marker)[0]
 old=subprocess.check_output(['git','show',BASE+':'+file],cwd=ROOT).decode()
 assert prefix.rstrip()==old.rstrip(),'all prior source/guards preserved'
 pins=re.findall(r"/-- info: '"+re.escape(ns)+r"(\w+)' depends on axioms: \[([^\]]*)\] -/\s*#guard_msgs in\s*#print axioms "+re.escape(ns)+r"\1",text)
 pins=[(n,a) for n,a in pins if n in names]
 assert len(pins)==len(names) and {n for n,_ in pins}==set(names)
 assert all(set(re.findall(r'[\w.]+',a))=={'propext','Classical.choice','Quot.sound'} for _,a in pins)
def main():
 assert len(sys.argv)==3
 count=0
 for file,folder in zip(CONFIG,sys.argv[1:]):
  run=pathlib.Path(folder);source=(ROOT/file).read_bytes();before=json.loads((run/'before.json').read_text());result=json.loads((run/'result.json').read_text());log=(run/'build.log').read_bytes();bindings=json.loads((run/'log-bindings.json').read_text());raw=(run/'raw.log').read_bytes()
  validate(file,source,before,result,log,bindings,raw)
  def reject(s=source,b=before,r=result,l=log,k=bindings,w=raw):
   nonlocal count
   try:validate(file,s,b,r,l,k,w)
   except AssertionError:count+=1;return
   raise AssertionError('corruption accepted')
  reject(s=source+b' ')
  for key,value in [('actual_exit',1),('source_and_controls_checked',False)]:
   bad=copy.deepcopy(result);bad[key]=value;reject(r=bad)
  bad=copy.deepcopy(before);other=next(p for p in CONFIG if p!=file);bad['controls']['/workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/coord-access/current-file.txt']=sha((str(ROOT/other)+'\n').encode());reject(b=bad)
  bad=copy.deepcopy(before);bad['peer']['published_head']='0'*40;reject(b=bad)
  reject(w=raw+b'x')
  ns,_,names=CONFIG[file]
  for old,new in [(b'#guard_msgs in\n#print axioms '+ns.encode()+names[0].encode(),b'#print axioms '+ns.encode()+names[0].encode()),(b"'"+ns.encode()+names[0].encode()+b"' depends on axioms: [propext,",b"'"+ns.encode()+names[0].encode()+b"' depends on axioms: [sorryAx,")]:
   altered=source.replace(old,new);assert altered!=source;bad=copy.deepcopy(before);bad['source'][file]=sha(altered);reject(s=altered,b=bad)
 print(f'PASS paired exact18 guards, all predecessor bytes, exact checked targets/policy/raw and decoded logs/source/resources; {count} corruption controls; no Lean/Docker')
if __name__=='__main__':main()
