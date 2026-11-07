"""Guard changed-source native false-assertion, vacuity and exact-spec regressions.
Replays only freshly compiled negative-control wires; no timing comparison.
"""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path.cwd();out=Path('/workspace/scratch/browser-chain/environment/native-negatives');out.mkdir(exist_ok=False)
base=Path('/workspace/scratch/browser-chain/environment/negative-controls');requests=[json.loads(x) for x in (base/'browser-control-attempts.jsonl').read_text().splitlines()];records=json.loads((base/'browser-control-completion.json').read_text())['requests'];assert len(requests)==len(records)==7
sha=lambda b:hashlib.sha256(b).hexdigest();binary=root/'.lake/native-browser-environment/native/direct-check';manifest=json.loads(binary.with_name('build.json').read_text());assert sha(binary.read_bytes())==manifest['executable']
for a,b in zip(requests,records):
 assert sha(a['wire'].encode())==a['wireSha256']==b['wireSha256'];assert sha(Path(b['compilerHeader']['source']).read_bytes())==a['sourceHash']==b['sourceHash']
command=['strace','-f','-qq','-e','trace=%file,%process,%network','-o',str(out/'native.strace'),str(binary)];run=subprocess.run(command,input=''.join(x['wire']+'\n' for x in requests),text=True,capture_output=True,timeout=600000);(out/'replies.jsonl').write_text(run.stdout);assert run.returncode==0,run.stderr
rows=[json.loads(x) for x in run.stdout.splitlines()];assert rows.pop(0)=={'ready':True};assert len(rows)==7;count=0
for request,reply in zip(requests,rows):
 assert len(reply['results'])==len(request['expected'])
 for (name,statuses),actual in zip(request['expected'],reply['results']):
  assert actual['function']==name and actual['status'] in statuses,(name,actual);count+=1
  if actual['status']=='refuted':assert actual['verification']=='direct' and actual['counterexample']['certified'] is False
assert count==14
forbidden=[x for x in (out/'native.strace').read_text().splitlines() if re.search(r'\.(olean|ilean)(\W|$)|execve\("[^"]*/(lean|lake)"',x)];assert not forbidden
(out/'results.json').write_text(json.dumps({'passed':True,'requestGroups':7,'verdicts':14,'binarySha256':manifest['executable'],'expected':[x['expected'] for x in requests],'replies':rows,'forbiddenLoads':forbidden,'boundary':'Trusted compiled-checker source-identified negatives/spec observations;not source preservation,proofterms or timing acceptance.'},indent=2)+'\n');print('PASS14native negative/vacuity/spec verdicts')
