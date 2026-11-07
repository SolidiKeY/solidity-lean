"""Guards stack/cost diagnosis against historical-binary and timing-causality overclaims.
Only reads authenticated saved evidence and binary structure; no binary execution.
"""
from pathlib import Path
import argparse,collections,hashlib,json,math,re,statistics,subprocess,tarfile
ROOT=Path(__file__).resolve().parents[3];OWNED=Path(__file__).resolve().parent
INBOX=OWNED/'artifacts/native-intake';SOURCE='0140eb13b2f122d421deb07a19575a6801b21dfc'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def wasm_layout(data):
 assert data[:8]==b'\0asm\x01\0\0\0','WASM header'
 def leb(pos):
  value=shift=0
  while True:
   assert pos<len(data) and shift<35,'truncated/oversized LEB'
   byte=data[pos];pos+=1;value|=(byte&127)<<shift;shift+=7
   if byte<128:return value,pos
 def name(pos):
  length,pos=leb(pos);assert pos+length<=len(data);return data[pos:pos+length].decode(),pos+length
 i=8;imports=0;bodies=[];exports={};custom=[]
 while i<len(data):
  sid=data[i];length,start=leb(i+1);end=start+length;assert end<=len(data),'section length'
  if sid==0:
   n,_=name(start);custom.append(n)
  elif sid==2:
   count,q=leb(start)
   for _ in range(count):
    _,q=name(q);_,q=name(q);assert data[q]==0,'target imports must be functions';_,q=leb(q+1);imports+=1
   assert q==end
  elif sid==7:
   count,q=leb(start)
   for _ in range(count):
    n,q=name(q);kind=data[q];index,q=leb(q+1)
    if kind==0:exports[index]=n
   assert q==end
  elif sid==10:
   count,q=leb(start)
   for _ in range(count):
    size,q=leb(q);assert q+size<=end;bodies.append((q,q+size));q+=size
   assert q==end
  i=end
 return {'imports':imports,'bodies':bodies,'exports':exports,'customSections':custom}
def frame_locations(stack,layout):
 rows=[]
 for index,offset in re.findall(r'wasm-function\[(\d+)\]:0x([0-9a-f]+)',stack):
  index=int(index);offset=int(offset,16);local=index-layout['imports'];assert 0<=local<len(layout['bodies'])
  start,end=layout['bodies'][local];assert start<=offset<end,'stack offset outside indexed function'
  rows.append({'index':index,'offset':offset,'bodyStart':start,'bodyEnd':end,'export':layout['exports'].get(index)})
 assert rows,'no wasm stack frames';return rows
def benchmark_summary(trials):
 groups=collections.defaultdict(list)
 for row in trials:groups[row['name']].append(row['wallMs'])
 assert len(trials)==249 and len(groups)==83 and {len(v) for v in groups.values()}=={3}
 medians=sorted(statistics.median(v) for v in groups.values())
 return {'requests':249,'functions':83,'rounds':3,'medianMs':statistics.median(medians),'p95Ms':medians[math.floor(len(medians)*.95)]}
def diagnose():
 request=json.loads((INBOX/'delivery-request.json').read_text())
 assert sha((INBOX/'delivery-request.json').read_bytes())=='d75cbfd8d9b8550f99db4dfdc5507cbf1fa1cf3f47df2ab124654375b45f406f'
 assert request['sourceBuildHead']==SOURCE
 for row in request['files']:
  p=INBOX/row['member'];assert p.stat().st_size==row['bytes'] and sha(p.read_bytes())==row['sha256']
 native=json.loads((INBOX/'.lake/native-browser-h81/native/build.json').read_text())
 wasm=json.loads((INBOX/'.lake/native-browser-h81/direct/build.json').read_text())
 assert native['sourceFiles']==wasm['sourceFiles'] and len(native['sourceFiles'])==343
 assert len({r['module'] for r in native['sourceFiles']})==343,'duplicate historical source module'
 for name,head in [('native-browser-h81-handoff-3efa0a3832de','3efa0a3832de30e514ca9d2fd286f129c0ca9984'),('native-browser-b-journal-handoff-cc62220dcf1a','cc62220dcf1a47771536d75599b0ef588d143d62')]:
  h=json.loads((INBOX/'.lake'/name/'handoff.json').read_text());assert h['sourceBuildHead']==SOURCE and h['head']==head
 for row in native['sourceFiles']:
  path=row['module'].replace('.','/')+'.lean'
  raw=subprocess.check_output(['git','show',SOURCE+':'+path],cwd=ROOT)
  assert sha(raw)==row['sourceSha256'],('historical source mismatch',path)
 assert native['closure']==wasm['closure'] and native['closure']['modules']==206
 binary=(INBOX/'.lake/native-browser-h81/direct/direct.wasm').read_bytes()
 assert sha(binary)==wasm['wasm'] and sha((INBOX/'.lake/native-browser-h81/direct/direct.js').read_bytes())==wasm['javascript']
 assert sha((INBOX/'.lake/native-browser-h81/native/direct-check').read_bytes())==native['executable']
 with tarfile.open(INBOX/'.lake/native-browser-h81-evidence/h81-evidence.tar.gz','r:gz') as archive:
  names=archive.getnames()
  def load(suffix):
   matches=[n for n in names if n.endswith(suffix)];assert len(matches)==1,suffix
   return json.load(archive.extractfile(matches[0]))
  selected=load('/h81-closure/selected-C-objects.json')
  assert len(selected)==len(wasm['modules'])==206 and len({r['module'] for r in selected})==206
  assert len({r['module'] for r in wasm['modules']})==206
  nativeC={r['module']:r['compiledCSha256'] for r in selected};wasmC={r['module']:r['compiledCSha256'] for r in wasm['modules']}
  assert nativeC==wasmC,'recorded compiled C hash parity'
  control=load('/h81-browser-controls/browser-control-completion.json')
  assert control['binarySha256']==wasm['wasm']
  failure=next(r for r in control['requests'] if r['name']=='invariantCountsToBound')
  assert failure['reply']['workerError']['message']=='Maximum call stack size exceeded'
  fixture=archive.extractfile(next(n for n in names if n.endswith('/browser-control-completion-inputs/control-4.ast.json'))).read()
  source=archive.extractfile(next(n for n in names if n.endswith('/browser-control-completion-inputs/control-4.sol'))).read()
  assert sha(fixture)==failure['fixtureSha256'] and sha(source)==failure['sourceHash']
  layout=wasm_layout(binary);frames=frame_locations(failure['reply']['workerError']['stack'],layout)
  assert frames[0]['export']=='malloc' and 'name' not in layout['customSections']
  stops=load('/h81-evidence/performance-stops.json');slow=load('/h81-native/slowdown-investigation.json')
  n=load('/h81-native/checks/native.json');b=load('/h81-browser-benchmark/browser.json')
  assert n['executableSha256']==native['executable']
  summaries={'nativeAst':benchmark_summary(n['trials']),'browser':benchmark_summary(b['trials'])}
  for key,summary in summaries.items():
   for metric in ['medianMs','p95Ms']:assert summary[metric]==stops['comparisons'][key]['current'][metric]
  assert n['startupMs']==stops['comparisons']['nativeAst']['current']['startupMs'] and b['startupMs']==stops['comparisons']['browser']['current']['startupMs']
  fields=['function','reading','reason','sourceId','status','tag','verification']
  nativeRows={(r['name'],r['round']):r for r in n['trials']};browserRows={(r['name'],r['round']):r for r in b['trials']}
  assert len(nativeRows)==len(browserRows)==249 and nativeRows.keys()==browserRows.keys()
  project=lambda rows:[{k:r[k] for k in fields} for r in rows]
  for key,row in nativeRows.items():
   other=browserRows[key];assert row['sourceHash']==other['sourceHash']
   assert project(row['result']['results'])==project(other['results'])
  assert len(slow['cases'])==83 and slow['sameSourceCount']==83
  wire=statistics.median(r['wireRatio'] for r in slow['cases']);assert wire==slow['medianWireRatio']
 return {'regression':'Historical stack/native cost diagnosis without stale freshness or causal claims','sourceBuildHead':SOURCE,'verifiedHistoricalSourceFiles':343,'reportedSelectedCModules':206,'coreResultProjectionParityRequests':249,'stack':{'functionImports':layout['imports'],'definedFunctions':len(layout['bodies']),'frames':frames,'repeatedIndices':{str(k):v for k,v in collections.Counter(r['index'] for r in frames).items() if v>1},'symbolization':'Top frame is exported malloc. Internal functions unnamed: exact WASM has no name section. No attribution to AST traversal, proof search or a specific source function yet.','inputSourceSha256':failure['sourceHash'],'inputFixtureSha256':failure['fixtureSha256']},'savedTimingSummaries':summaries,'retainedStopRatios':{k:v['ratios'] for k,v in stops['comparisons'].items()},'medianWireRatio':wire,'costConclusion':'Source/payload/runtime confounded; no causal attribution. Short-case overhead hypothesis remains unproved. No unchanged STOP rerun.','boundary':'Static authenticated saved evidence only.343source hashes match0140; no206object-byte verification, source/compiler/native correctness, current957e freshness, new runtime acceptance or benchmark execution.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--report',type=Path);a=p.parse_args();r=diagnose()
 if a.report:a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps({k:v for k,v in r.items() if k!='stack'}));print(json.dumps(r['stack']))
