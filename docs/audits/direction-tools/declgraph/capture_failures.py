#!/usr/bin/env python3
"""Receipt-bound driver failure inventory, not semantic root replay.
Only explicit native/driver diagnostics are categorized. A missing observation
never establishes unusedness, a failed theorem, or a deletable source line.
"""
if not __debug__:raise SystemExit('OPTIMIZED_PYTHON_UNSUPPORTED')
import argparse,collections,hashlib,json,pathlib,re,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
Q=runpy.run_path(str(HERE/'capture_cached_checks.py'));API=Q['API'];SHA=Q['SHA']
PRODUCERS=('capture_cached_checks.py','capture_compact.py','CompactRoots.lean','compact_records.py','run_snapshot_roots.py','audit.py','modules.txt','source-check-syntax.json','snapshot-root-summary.json')
def diagnosis(driver,native,receipt_present):
 if receipt_present:return 'unvalidated_native_receipt_present'
 if native.strip()=='SNAPSHOT_ROOTS_UNSUPPORTED incomplete info context':return 'explicit_unsupported_info_context'
 if 'error: sol_close_nonlin: bounded search stopped; original goal retained' in native:return 'explicit_bounded_search_stop'
 if 'subprocess.TimeoutExpired:' in driver:return 'driver_reported_subprocess_timeout'
 return 'unclassified_failure'
def raw_lf_lines(text):return text.count('\n')+int(bool(text) and not text.endswith('\n'))
def safe_destinations(source,view,captures,out,evidence,limit,*,check=False):
 source,view,captures,out,evidence=(pathlib.Path(x).resolve() for x in (source,view,captures,out,evidence))
 assert isinstance(limit,int) and limit>0
 assert out==HERE/f'capture-failures-prefix{limit}.json','Only the designated checker summary may be written'
 for protected in (HERE.parents[3],source,view,captures):
  assert not evidence.is_relative_to(protected) and not protected.is_relative_to(evidence),'Evidence overlaps protected source/code/cache'
 assert check or not evidence.exists(),'Fresh private evidence path required'

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--captures',type=pathlib.Path,required=True);p.add_argument('--limit',type=int,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--evidence',type=pathlib.Path,required=True);p.add_argument('--prior-runner-commit',action='append',default=[]);p.add_argument('--check',action='store_true');a=p.parse_args()
 for n in ('source_root','view','captures','out','evidence'):setattr(a,n,getattr(a,n).resolve())
 with Q['writer_lease']():
  safe_destinations(a.source_root,a.view,a.captures,a.out,a.evidence,a.limit,check=a.check)
  src=API['assert_sources'](a.source_root);queue,reused,uncached=Q['selection']();assert 0<a.limit<=len(queue)
  producers={n:SHA(HERE/n) for n in PRODUCERS};producers['capture_failures.py']=SHA(HERE/'capture_failures.py');allowed={producers['capture_cached_checks.py']};inputs={}
  for commit in a.prior_runner_commit:
   assert re.fullmatch('[0-9a-f]{40}',commit)
   subprocess.run(['git','merge-base','--is-ancestor',commit,'HEAD'],cwd=HERE.parents[3],check=True)
   blob=subprocess.check_output(['git','show',commit+':docs/audits/direction-tools/declgraph/capture_cached_checks.py'],cwd=HERE.parents[3]);allowed.add(hashlib.sha256(blob).hexdigest())
  def remember(path):
   h=SHA(path);assert str(path) not in inputs or inputs[str(path)]==h;inputs[str(path)]=h
  rows=[];counts=collections.Counter();areas=collections.defaultdict(collections.Counter);directories=collections.defaultdict(collections.Counter);provenance=collections.defaultdict(collections.Counter)
  for path in queue[:a.limit]:
   stem=hashlib.sha256(path.encode()).hexdigest()[:20];directory=a.captures/stem;status_file=a.captures/(stem+'.status.json');driver_file=a.captures/(stem+'.driver.log');status=json.loads(status_file.read_text());remember(status_file);remember(driver_file)
   command=['python3','-I',str(HERE/'capture_compact.py'),'--source-root',str(a.source_root),'--view',str(a.view),'--capture',str(directory),'--file',path,'--out',str(a.captures/(stem+'.summary.json'))]
   Q['validate_status'](status,dict(path=path,command=command,source_sha256=SHA(a.source_root/path),producers={n:producers[n] for n in PRODUCERS}),allowed);assert status['log_sha256']==inputs[str(driver_file)]
   category='driver_exit_zero_unreplayed_here';receipt=directory/'receipt.json';native_file=directory/'capture.log'
   if status['exit_code']:
    native=''
    if native_file.exists():remember(native_file);native=native_file.read_text()
    if receipt.exists():remember(receipt)
    category=diagnosis(driver_file.read_text(),native,receipt.exists())
   row=dict(path=path,exit_code=status['exit_code'],category=category,provenance=API['provenance'](path,src[path]),source_raw_lf_lines=raw_lf_lines(src[path]))
   rows.append(row);counts[category]+=1;areas['/'.join(path.split('/')[:2])][category]+=1;directories[str(pathlib.PurePosixPath(path).parent)][category]+=1;provenance[row['provenance']][category]+=1
  def plain(d):return {k:dict(sorted(v.items())) for k,v in sorted(d.items())}
  result=dict(base=API['BASE'],status='partial',selected_files=len(rows),planned_queue_files=len(queue),categories=dict(sorted(counts.items())),areas=plain(areas),directories=plain(directories),provenance=plain(provenance),files=rows,deletable_now_verified_lines=0,boundaries=['Driver exit-zero rows are not semantically replayed by this inventory; accepted replay/join outputs remain separate.','Unsupported context is an exporter diagnostic, not proof failure or evidence of unused declarations. Timeout and bounded-search categories report explicit diagnostics only; they do not establish false theorems.','Partial native output from unsuccessful captures is excluded; no dependencies are recovered or certified here. Receipt existence is not validated native success.','Source-file line counts describe coverage inventory only, not declaration spans, used/unused lines or removable code.','Provenance labels distinguish marked-generated and unresolved generators; untraced does not mean handwritten.','H347 pinned baseline retained; verification blocked, additive v2 unadopted, zero deletion certifications.'])
  body=json.dumps(result,sort_keys=True,indent=2)+'\n';assert len(body.encode())<1000000
  assert producers=={n:SHA(HERE/n) for n in producers} and all(SHA(pathlib.Path(n))==h for n,h in inputs.items());API['assert_sources'](a.source_root)
  proof=dict(base=API['BASE'],source_root=str(a.source_root),view=str(a.view),captures=str(a.captures),limit=a.limit,producers=producers,inputs=inputs,output_sha256=hashlib.sha256(body.encode()).hexdigest())
  if a.check:assert a.out.read_text()==body and json.loads(a.evidence.read_text())==proof,'Failure inventory drift'
  else:
   Q['atomic_text'](a.out,body);Q['atomic_json'](a.evidence,proof)
   assert SHA(a.out)==proof['output_sha256'] and json.loads(a.evidence.read_text())==proof,'Published failure inventory drift'
   assert producers=={n:SHA(HERE/n) for n in producers} and all(SHA(pathlib.Path(n))==h for n,h in inputs.items()),'Protected input changed during publication'
   API['assert_sources'](a.source_root)
  print('CAPTURE_FAILURE_INVENTORY_PASS',len(rows),json.dumps(dict(sorted(counts.items())),sort_keys=True))
if __name__=='__main__':main()
