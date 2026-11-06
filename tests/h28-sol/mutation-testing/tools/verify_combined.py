#!/usr/bin/env python3
"""Authenticate and replay the saved combined pilot; never grants full acceptance."""
from pathlib import Path
import argparse,hashlib,json,subprocess,tarfile
from archive_io import read_json,require
import checked
from engine import summarize


def digest(data):return hashlib.sha256(data).hexdigest()


def verify(repo, profile='combined'):
 profiles={'combined':('combined_proof_pack','combined-pilot.json',17,13),
           'rollback':('rollback_proof_pack','rollback-pilot.json',2,1),
           'frame':('frame_proof_pack','frame-pilot.json',2,1),
           'selected':('selected_proof_pack','selected-suite.json',19,15)}
 require(profile in profiles,'unsupported proof profile')
 pin_key,manifest_name,case_count,scored_count=profiles[profile]
 pin=read_json(repo/'tests/h28-sol/mutation-testing/bulk-data.json',repo)[pin_key]
 archive=Path(pin['archive']);require(archive.stat().st_size==pin['bytes'],'archive size mismatch')
 with archive.open('rb') as f:
  h=hashlib.sha256()
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 require(h.hexdigest()==pin['sha256'],'archive hash mismatch')
 if 'member_manifest' in pin:
  from verify_bulk import verify_h44_member_manifest
  verify_h44_member_manifest(repo,pin)
 with tarfile.open(archive,'r:gz') as tar:
  members={}
  for m in tar:
   require(m.isfile() and m.name not in members and not m.name.startswith('/') and '..' not in Path(m.name).parts,'unsafe archive member')
   members[m.name]=m
  require(len(members)==pin['members'],'archive member count mismatch')
  def read(name):return tar.extractfile(members[name]).read()
  expected={}
  for line in read('SHA256SUMS').decode().splitlines():
   sha,name=line.split('  ',1);require(name not in expected,'duplicate checksum');expected[name]=sha
  require(set(members)==set(expected)|{'SHA256SUMS'},'archive membership mismatch')
  for name,sha in expected.items():require(digest(read(name))==sha,'member checksum mismatch: '+name)
  m=json.loads(read('run/manifest.json'));r=json.loads(read('run/result.json'));catalog=json.loads(read('catalog.json'))
  frozen=subprocess.check_output(['git','show',r['run_head']+':tests/h28-sol/mutation-testing/manifests/'+manifest_name],cwd=repo)
  require(read('run/manifest.json')==frozen,'manifest differs from committed run head')
  require(r['run_head']==pin['input_head'] and r['base']==m['base'],'run identity mismatch')
  require(r['runner_cases_complete'] and not r['scope_complete'] and not r['unrun'],'run incomplete or scope overclaim')
  summary=summarize(r['records'],m['cases'])
  require(all(r[k]==v for k,v in summary.items()),'summary replay mismatch')
  require(len(r['records'])==case_count and r['denominator']==r['killed']==scored_count and r['score']==1,profile+' outcomes changed')
  cases={c['id']:c for c in m['cases']};checks=exports=artifacts=0
  for rec in r['records']:
   c=cases[rec['id']];prefix='run/'+rec['id']+'/'
   phases={'baseline-compile','baseline-oracle','mutant-compile'}
   if c['kind']=='equivalent-control':phases.add('baseline-equivalence')
   elif c['kind']!='invalid-control':phases.add('baseline-witness')
   if c['kind']=='runner-survivor-control':phases.add('baseline-regression')
   if c['kind']!='invalid-control':
    phases.add('mutant-oracle');phases.add('mutant-equivalence' if c['kind']=='equivalent-control' else 'mutant-witness')
   if c['kind']=='runner-survivor-control':phases.add('mutant-regression')
   require(set(rec['checks'])==phases,'required check phases mismatch')
   positive={phase for phase,res in rec['checks'].items() if res['exit']==0}
   require(set(rec['compiled_artifacts'])==positive,'required successful outputs mismatch')
   actual_outputs={n for n in members if n.startswith(prefix) and n.endswith('.olean')}
   require(actual_outputs=={prefix+a['path'] for a in rec['compiled_artifacts'].values()},'unreferenced/negative compiled output')
   for field in ('oracle','witness','equivalence','regression'):
    if field in c:
     source=read('sources/'+c[field]);require(digest(source)==c[field+'_sha256'],'fixture identity mismatch')
     require(source==subprocess.check_output(['git','show',r['run_head']+':'+c[field]],cwd=repo),'fixture differs from committed run head')
   for phase,res in rec['checks'].items():
    log=read(prefix+phase+'.log').decode();require(digest(log.encode())==res['log_sha256'],'log hash mismatch')
    require(res['kind']=='exit' and res['cleanup_confirmed'] and res['memory_limit'] in (2*1024**3,4*1024**3,6*1024**3) and res['swap_limit']==0,'runtime outcome/bound mismatch')
    require(res['runtime_lean_sha256']==m['runtime_lean_sha256'] and res['measurement_binary_sha256']==m['measurement_binary_sha256'],'runtime identity mismatch')
    require(res['failure'] is None and not res['oom_killed'] and res['reserved_before']>=4*1024**3 and '-j1' in res['lean_argv'] and '-o' in res['lean_argv'] and '--network=none' in res['argv'],'resource/serial guarantee mismatch')
    require(res['lean_measurement']['signal']==0 and res['lean_measurement']['exit']==res['exit'],'measurement outcome mismatch')
    checks+=1;field=phase.split('-',1)[1]
    if field=='compile':
     if res['exit']==0:checked.success(res,log)
     else:
      require(rec['status']=='invalid-compilation' and phase=='mutant-compile' and res['exit']==1,'unexpected compile failure')
      errors=[x for x in checked.messages(log) if x['severity']=='error']
      require(errors and all(x['fileName']==c['target'] for x in errors),'invalid compilation attribution mismatch')
     continue
    source=read('sources/'+c[field]).decode()
    if res['exit']==0:
     cert=checked.success(res,log,c[field+'_declarations']);cert['all_owned_axioms']=checked.all_owned_axioms(res,log,source)
     require(cert==rec['validation'][phase],'certificate replay mismatch')
     require({n:digest(s.encode()) for n,s in cert['signatures'].items()}==c[field+'_signature_sha256'],'signature mismatch')
     exports+=len(cert['all_owned_axioms'])
    else:
     lines=[i for i,line in enumerate(source.splitlines(),1) if line.startswith('theorem source_link :')]
     require(len(lines)==1,'source-link inventory mismatch')
     require(checked.source_link_rejection(res,log,c[field],lines[0])==rec['validation'][phase],'rejection replay mismatch')
   for phase,a in rec['compiled_artifacts'].items():
    field=phase.split('-',1)[1];source=c['target'] if field=='compile' else c[field]
    source_data=subprocess.check_output(['git','show',m['base']+':'+source],cwd=repo) if field=='compile' else read('sources/'+source)
    if field=='compile' and phase.startswith('mutant-'):source_data=source_data.replace(c['old'].encode(),c['new'].encode(),1)
    require(a['phase']==phase and a['source']==source and a['source_sha256']==digest(source_data),'compiled output phase/source mismatch')
    data=read(prefix+a['path']);require(a['bytes']>0 and len(data)==a['bytes'] and digest(data)==a['sha256'],'compiled output mismatch');artifacts+=1
   if 'mutation' in rec:
    original=subprocess.check_output(['git','show',m['base']+':'+c['target']],cwd=repo)
    require(digest(original)==c['target_sha256']==rec['mutation']['before_sha256'],'original mutation source mismatch')
    require(original.count(c['old'].encode())==1,'nonunique edit')
    require(digest(original.replace(c['old'].encode(),c['new'].encode(),1))==c['mutant_sha256']==rec['mutation']['after_sha256'],'mutation attribution mismatch')
    require(digest(read(prefix+'mutant.patch'))==rec['mutation']['diff_sha256'],'mutation diff mismatch')
  require(checks==pin['check_count']==catalog['check_count'] and exports==pin['axiom_export_count']==catalog['axiom_export_count'] and artifacts==pin['compiled_artifact_count'],'evidence counts mismatch')
  if profile == 'selected':
   from selected_accounting import verify as verify_accounting
   verify_accounting(repo, read, r, m, set(members))
 for key in ('dependency_pack','prior_dependency_pack'):
  dep=pin[key];h=hashlib.sha256()
  with open(dep['archive'],'rb') as stream:
   for b in iter(lambda:stream.read(1048576),b''):h.update(b)
  require(h.hexdigest()==dep['sha256'],'dependency archive mismatch')
 return {'status':'pass','archive':str(archive),'checks':checks,'axiom_exports':exports,'compiled_artifacts':artifacts,'scope_complete':False,'coordinator_pull_observed':False}


if __name__=='__main__':
 repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
 parser=argparse.ArgumentParser();parser.add_argument('--profile',choices=('combined','rollback','frame','selected'),default='combined');args=parser.parse_args()
 print(json.dumps(verify(repo,args.profile),indent=2))
