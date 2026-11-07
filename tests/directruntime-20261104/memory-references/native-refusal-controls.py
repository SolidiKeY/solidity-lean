"""Controlled malformed-AST/type-error API refusals; not fresh valid Solidity cases."""
import hashlib,json,os,pathlib,re,subprocess,sys
root=pathlib.Path(__file__).resolve().parent;binary=pathlib.Path(sys.argv[1]).resolve();out=pathlib.Path(sys.argv[2]).resolve();out.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
assert sha(binary)==json.loads((binary.parent/'build.json').read_text())['executable']
rows=[r for r in json.loads((root/'evidence/admission-inputs.json').read_text()) if not r.get('accept') or not r.get('typed',False)]
assert len(rows)==22
requests=[];anchors=[]
for row in rows:
 file=root/row['path'];assert sha(file)==row['normalizedSha256']
 ast=json.loads(file.read_text())['sources']['Identity.sol']['ast'];contract=next(n for n in ast['nodes'] if n.get('nodeType')=='ContractDefinition');fn=next(n for n in contract['nodes'] if n.get('nodeType')=='FunctionDefinition')
 requests.append({'contract':contract,'function':fn['name'],'sourceId':fn['id']});anchors.append({'input':row['input'],'inputSha256':sha(file),'function':fn['name'],'sourceId':fn['id']})
payload=''.join(json.dumps(x,separators=(',',':'))+'\n' for x in requests);(out/'requests.jsonl').write_text(payload)
empty=out/'empty-cwd';empty.mkdir(exist_ok=True);env=dict(os.environ)
for name in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(name,None)
trace=out/'runtime.strace';run=subprocess.run(['/usr/bin/strace','-f','-e','trace=file,process,network','-o',str(trace),str(binary)],input=payload,text=True,capture_output=True,cwd=empty,env=env,timeout=120)
(out/'stdout').write_text(run.stdout);(out/'stderr').write_text(run.stderr);assert run.returncode==0
lines=[json.loads(x) for x in run.stdout.splitlines()];assert lines[0]=={'ready':True};assert len(lines)==23
observations=[]
for anchor,value in zip(anchors,lines[1:]):
 if 'results' in value:
  assert len(value['results'])==1;row=value['results'][0];assert row['function']==anchor['function'] and row['sourceId']==anchor['sourceId'];assert row['status']=='unsupported',(anchor,value)
 else:assert isinstance(value.get('gap'),str),(anchor,value)
 observations.append({**anchor,'result':value})
text=trace.read_text();assert not re.search(r'\.(?:olean|ilean|lean)(?:["/ ]|$)',text)
assert re.findall(r'execve\("([^"]+)"',text)==[str(binary)];assert not re.search(r'\bexecveat\(',text)
assert not re.search(r'\b(?:socket|socketpair|connect|accept|accept4|bind|listen|sendto|recvfrom|sendmsg|recvmsg|sendmmsg|recvmmsg|shutdown|getsockname|getpeername|setsockopt|getsockopt)\(',text)
result={'binary':str(binary),'binarySha256':sha(binary),'refusals':len(observations),'exit':run.returncode,'observations':observations,'traceSha256':sha(trace),'boundary':'20 controlled malformed ASTs and two coherent type-error ASTs; separate from the 84 freshly compiled valid-source requests. Trace checks are observations, not exhaustive binary closure.'}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS22 native API refusals (20 malformed,2 type errors)')
