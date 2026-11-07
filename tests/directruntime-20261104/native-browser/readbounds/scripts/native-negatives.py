"""Guard changed-source native false-assertion, vacuity and exact-spec regressions.
Replays only freshly compiled negative-control wires; no timing comparison.
"""
from pathlib import Path
import hashlib,json,re,subprocess
import fcntl,importlib.util,os,time
if not __debug__:raise RuntimeError("replay validation requires Python assertions enabled")

def replay():
 root=Path.cwd();out=Path('/workspace/scratch/browser-chain/readbounds-6513/recovered/native-negatives');out.mkdir(exist_ok=False)
 base=Path('/workspace/scratch/browser-chain/readbounds-6513/recovered/negative-controls');requests=[json.loads(x) for x in (base/'browser-control-attempts.jsonl').read_text().splitlines()];records=json.loads((base/'browser-control-completion.json').read_text())['requests'];assert len(requests)==len(records)==7
 sha=lambda b:hashlib.sha256(b).hexdigest();binary=root/'.lake/native-browser-readbounds-6513/native/direct-check';manifest=json.loads(binary.with_name('build.json').read_text());assert sha(binary.read_bytes())==manifest['executable']
 for a,b in zip(requests,records):
  assert sha(a['wire'].encode())==a['wireSha256']==b['wireSha256'];assert sha(Path(b['compilerHeader']['source']).read_bytes())==a['sourceHash']==b['sourceHash']
 command=['strace','-f','-qq','-e','trace=%file,%process,%network','-o',str(out/'native.strace'),str(binary)];run=subprocess.run(command,input=''.join(x['wire']+'\n' for x in requests),text=True,capture_output=True,timeout=300);(out/'replies.jsonl').write_text(run.stdout);assert run.returncode==0,run.stderr
 rows=[json.loads(x) for x in run.stdout.splitlines()];assert rows.pop(0)=={'ready':True};assert len(rows)==7;count=0
 for request,reply in zip(requests,rows):
  assert len(reply['results'])==len(request['expected'])
  for (name,statuses),actual in zip(request['expected'],reply['results']):
   assert actual['function']==name and actual['status'] in statuses,(name,actual);count+=1
   if actual['status']=='refuted':assert actual['verification']=='direct' and actual['counterexample']['certified'] is False
 assert count==14
 forbidden=[x for x in (out/'native.strace').read_text().splitlines() if re.search(r'\.(olean|ilean)(\W|$)|execve\("[^"]*/(lean|lake)"',x)];assert not forbidden
 (out/'results.pending.json').write_text(json.dumps({'passed':False,'status':'provisional','requestGroups':7,'verdicts':14,'binarySha256':manifest['executable'],'expected':[x['expected'] for x in requests],'replies':rows,'forbiddenLoads':forbidden,'boundary':'Trusted compiled-checker source-identified negatives/spec observations;not source preservation,proofterms or timing acceptance.'},indent=2)+'\n');print('PROVISIONAL14native verdicts; awaiting parent deadline check')


def sync_directory(path):
 directory=os.open(path,os.O_RDONLY|os.O_DIRECTORY)
 try:os.fsync(directory)
 finally:os.close(directory)


def publish_result(pending,final,deadline):
 if time.monotonic_ns()>=deadline:raise TimeoutError('native replay deadline expired before publication')
 data=json.loads(pending.read_bytes())
 if data.get('passed') is not False or data.get('status')!='provisional':raise ValueError('expected provisional replay output')
 data.update(passed=True,status='parent-deadline-checked',deadlineMonotonicNs=deadline)
 temporary=final.with_name(final.name+'.seal.tmp');published=False;created_temporary=False
 try:
  with temporary.open('x') as f:
   created_temporary=True
   json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
  if time.monotonic_ns()>=deadline:raise TimeoutError('native replay deadline expired while sealing')
  os.link(temporary,final);published=True;sync_directory(final.parent)
  if time.monotonic_ns()>=deadline:raise TimeoutError('native replay publication deadline overrun')
  temporary.unlink();created_temporary=False;sync_directory(final.parent)
  if time.monotonic_ns()>=deadline:raise TimeoutError('native replay finalization deadline overrun')
 except BaseException:
  if published:
   try:final.unlink();sync_directory(final.parent)
   except BaseException as error:
    # Preserve provisional/seal facts; never claim durable PASS retraction.
    raise RuntimeError('native replay result retraction unresolved; invocation exit is authoritative') from error
  if created_temporary:temporary.unlink();sync_directory(final.parent)
  raise


def main():
 deadline=time.monotonic_ns()+300_000_000_000
 helper=Path(__file__).resolve().parents[1]/'invocation-deadline.py'
 spec=importlib.util.spec_from_file_location('native_replay_deadline',helper)
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a') as lock:
  while True:
   if time.monotonic_ns()>=deadline:raise TimeoutError('native replay writer-lock deadline expired')
   try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);break
   except BlockingIOError:time.sleep(0.005)
  remaining=deadline-time.monotonic_ns()
  if remaining<=0:raise TimeoutError('native replay invocation deadline expired')
  module.execute(replay,budget_ns=remaining)
  out=Path('/workspace/scratch/browser-chain/readbounds-6513/recovered/native-negatives')
  publish_result(out/'results.pending.json',out/'results.json',deadline)
  print('PASS14native negative/vacuity/spec verdicts')

if __name__=='__main__':main()
