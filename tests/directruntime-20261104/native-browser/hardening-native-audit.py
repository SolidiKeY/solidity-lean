"""Fresh syscall audit plus exact allocated-section comparison; external evidence."""
import hashlib,json,pathlib,re,struct,subprocess,sys,os
root=pathlib.Path.cwd();out=root/os.environ.get('NATIVE_BROWSER_CHECK_OUTPUT','docs/benchmarks/directruntime-2026-11-04/hardening')
name=sys.argv[1] if len(sys.argv)>1 else 'native-audit'
assert re.fullmatch(r'[a-z0-9-]+',name)
destination=out/(name+'.json')
if destination.exists():raise SystemExit('refusing audit overwrite')
for suffix in ['-runtime.strace','-trace-results.jsonl','-trace-stderr.txt']:
 if (out/(name+suffix)).exists():raise SystemExit('refusing raw audit overwrite')
sha=lambda b:hashlib.sha256(b).hexdigest()
def file_sha(p):
 h=hashlib.sha256()
 with pathlib.Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def elf(p):
 b=p.read_bytes();assert b[:6]==b'\x7fELF\x02\x01'
 h=struct.unpack_from('<16sHHIQQQIHHHHHH',b);off,size,count,names=h[6],h[11],h[12],h[13]
 ss=[struct.unpack_from('<IIQQQQIIQQ',b,off+i*size) for i in range(count)]
 ns=ss[names];strings=b[ns[4]:ns[4]+ns[5]];sections={}
 for s in ss:
  if s[2]&2:
   name=strings[s[0]:].split(b'\0')[0].decode()
   sections[name]=dict(type=s[1],flags=s[2],address=s[3],size=s[5],sha256=None if s[1]==8 else sha(b[s[4]:s[4]+s[5]]))
 return dict(machine=h[2],entry=h[4],flags=h[7],programHeaders=[list(struct.unpack_from('<IIQQQQQQ',b,h[5]+i*h[9])) for i in range(h[10])],allocatedSections=sections)
binary=root/os.environ.get('NATIVE_BROWSER_NATIVE_OUTPUT','.lake/native-browser-hardening/native')/'direct-check';old=root/'.lake/direct-native/direct-check'
manifest=json.loads((binary.parent/'build.json').read_text());assert file_sha(binary)==manifest['executable']
for path,digest in manifest['buildInputs'].items():assert file_sha(path)==digest,path
for entry in manifest['sourceFiles']:
 assert file_sha(root/(entry['module'].replace('.','/')+'.lean'))==entry['sourceSha256']
 assert file_sha(root/'.lake/build/ir'/(entry['module'].replace('.','/')+'.c'))==entry['cSha256']
before=elf(old);after=elf(binary);assert before==after
original=root/'docs/benchmarks/directruntime-2026-11-04/before'
classification=json.loads((original/'native-stub-classification.json').read_text())
coarse=json.loads((original/'native-audit.json').read_text());assert file_sha(old)==coarse['binarySha256']
assert classification['passed'] is True
assert classification['binarySha256']==file_sha(old)
assert classification['coarseReceiptSha256']==file_sha(original/'native-audit.json')
assert classification['coarseReceiptPassed']==coarse['passed']
symbols=subprocess.check_output(['nm','-C','--defined-only',str(binary)],text=True)
blocked=re.compile(r"\b(?:lean_initialize|lean_import_modules|l_Lean_importModules|l_Lean_(?:Elab|Meta|Environment|Kernel)_\w*|initialize_Lean_(?:Elab|Meta|Environment|Kernel)\w*)\b|lean::(?:environment|type_checker|module_mgr)\b")
flags=[line for line in symbols.splitlines() if blocked.search(line)]
assert flags==coarse['blockedDefinedSymbols']
inputs=json.loads((out/'inputs/inputs.json').read_text());wire=[];requests=[]
for round in range(3):
 for trial in inputs['trials']:
  encoded=json.dumps(trial['request'],separators=(',',':'),ensure_ascii=False).encode()
  assert sha(encoded)==trial['requestSha256']
  assert file_sha(trial['source'])==trial['sourceHash']
  assert file_sha(trial['fixture'])==trial['fixtureSha256']
  wire.append(encoded+b'\n');requests.append(dict(round=round,name=trial['name'],sourceSha256=trial['sourceHash'],requestSha256=sha(encoded)))
trace=out/(name+'-runtime.strace');command=['strace','-f','-qq','-e','trace=%file,%process,%network','-o',str(trace),str(binary)]
run=subprocess.run(command,input=b''.join(wire),stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
(out/(name+'-trace-results.jsonl')).write_bytes(run.stdout);(out/(name+'-trace-stderr.txt')).write_bytes(run.stderr)
rows=[json.loads(line) for line in run.stdout.splitlines()];assert rows[0]=={'ready':True}
failures=[dict(index=i,reply=r) for i,r in enumerate(rows[1:]) if len(r.get('results',[]))!=1 or r['results'][0].get('function')!=requests[i]['name'] or r['results'][0].get('status')!='proved']
loads=[line for line in trace.read_text().splitlines() if re.search(r'\.(?:olean|ilean)(?:\W|$)|execve\("[^"]*/(?:lean|lake)"',line)]
report=dict(command=command,exitCode=run.returncode,binarySha256=file_sha(binary),baselineBinarySha256=file_sha(old),allocatedStateAndLoadLayoutEqual=True,elf=after,originalCoarseFlags=flags,classificationReceiptSha256=file_sha(original/'native-stub-classification.json'),classificationPassed=classification['passed'],classificationBinarySha256=classification['binarySha256'],expectedRequests=249,actualReplies=len(rows)-1,requests=requests,semanticFailures=failures,forbiddenRuntimeLoads=loads,traceSha256=file_sha(trace),boundary='Fresh untimed syscall observations and exact allocated code/data/layout comparison to the independently classified baseline. Not a general purity or semantic-equivalence proof; source hashes are external request provenance, not binary attestations.')
report['passed']=run.returncode==0 and len(rows)==250 and not failures and not loads
with destination.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['passed','binarySha256','actualReplies','forbiddenRuntimeLoads']}))
assert report['passed']
