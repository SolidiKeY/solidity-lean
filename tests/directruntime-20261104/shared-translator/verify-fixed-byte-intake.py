"""Guards H77 fixed-byte delivery against missing dependencies and freshness overclaims.
Reads saved evidence, Git blobs and binary structure only. No payload extraction,
execution, rebuild or timing rerun; address qualification remains separate.
"""
import argparse, collections, hashlib, importlib.util, json, subprocess, tarfile
from pathlib import Path
O=Path(__file__).resolve().parent
ROOT=O.parents[2]
DEFAULT=ROOT/'.lake/native-browser-fixed-byte-complete/handoff-data'
HANDOFF=ROOT/'.lake/native-browser-fixed-byte-handoff-14a39effa376/handoff.json'
HEAD='14a39effa3766c898e0cc2a8e291ff1732e3e2e2'
SOURCE='1b2bdb490054293c86cddb5e4b7fa15736bae25b'
PRODUCER='2738af99661d7ba582c92519b20d47bcba34a5a4'
PINS={'handoff.json':'bdb1e6be68f21b6b98f4ac54385df5d0673b0635a0b3b412354a4a7b1aa970f9',
'evidence.tar.gz':'9ec59168adb64fe764467dbff35950b9a625dd576d5a8e31efe42db3a79c6cb9',
'runtime-artifacts.tar.gz':'4ab29eebeeaa5e25fa354fc62712a4957be79212898eb6b457de8873abe1c2f1',
'evidence-files.json':'dbe64cffacae9b1f8c319e423fa53c0b97b5ac131af38e3e7dda95037864d5ea',
'runtime-files.json':'a798598d86f5ba94876e09f6a5824005e49c7da9c0a8d34194c4ab06dc45acce'}
def load(name,file):
 spec=importlib.util.spec_from_file_location(name,O/file)
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
common=load('shared_intake','verify-sourcebuild-intake.py')
layout_tools=load('saved_wasm_structure','diagnose-native-evidence.py')
require=common.require
def sha(raw):return hashlib.sha256(raw).hexdigest()
def indexed_archive(path,index_path,count):
 raw=index_path.read_bytes();records=json.loads(raw)
 require(len(records)==count,'index denominator')
 expected={r['path']:r for r in records};require(len(expected)==count,'duplicate index path')
 with tarfile.open(path,'r:gz') as tar:
  entries=common.members(tar)
  require(set(entries)==set(expected)|{index_path.name},'archive/index member set')
  require(tar.extractfile(index_path.name).read()==raw,'embedded index differs')
  result={}
  for name,record in expected.items():
   require(entries[name].size==record['bytes'],'indexed member size')
   data=tar.extractfile(name).read();require(sha(data)==record['sha256'],'indexed member hash')
   result[name]=data
 return result
def projection(row):
 result={k:v for k,v in row.items() if k!='boot'}
 reply=dict(result['reply']);reply.pop('timings',None);result['reply']=reply
 return result
def parity(observation,count,wasm):
 native=observation['native'];browser=observation['browser']
 require(len(native)==len(browser)==count,'request denominator')
 require(len({r.get('caseKey',r['name']) for r in native})==count,'duplicate request identity')
 require([projection(x) for x in native]==[projection(x) for x in browser],'saved request/result parity')
 for row in browser:require(row['boot']['build']==wasm,'browser binary identity')
 statuses=collections.Counter(r['status'] for row in native for r in row['reply']['results'])
 return {'requestsPerBackend':count,'savedWireAndResultParity':True,'statuses':dict(statuses)}
def verify(directory,handoff_path):
 paths={n:directory/n for n in PINS};paths['handoff.json']=handoff_path
 for name,path in paths.items():
  with path.open('rb') as stream:require(hashlib.file_digest(stream,'sha256').hexdigest()==PINS[name],'outer hash: '+name)
 handoff=json.loads(handoff_path.read_bytes())
 require((handoff['head'],handoff['sourceBuildHead'],handoff['producerHead'])==(HEAD,SOURCE,PRODUCER),'head identity')
 evidence=indexed_archive(directory/'evidence.tar.gz',directory/'evidence-files.json',875)
 runtime=indexed_archive(directory/'runtime-artifacts.tar.gz',directory/'runtime-files.json',5)
 native=json.loads(runtime['native/build.json']);wasm=json.loads(runtime['direct/build.json'])
 require(native['sourceFiles']==wasm['sourceFiles'] and len(native['sourceFiles'])==343,'recorded source parity')
 require(len({r['module'] for r in native['sourceFiles']})==343,'duplicate source module')
 for row in native['sourceFiles']:
  path=row['module'].replace('.','/')+'.lean'
  raw=subprocess.check_output(['git','show',SOURCE+':'+path],cwd=ROOT)
  require(sha(raw)==row['sourceSha256'],'Git source mismatch: '+path)
 producer=[]
 for row in native['sourceFiles']:
  if row['module'].startswith('Solidity.Frontend.ExecutableAst.') or row['module']=='Solidity.Tools.DirectRuntime':
   path=row['module'].replace('.','/')+'.lean'
   require(sha(subprocess.check_output(['git','show',PRODUCER+':'+path],cwd=ROOT))==row['sourceSha256'],'producer dependency mismatch')
   producer.append(row['module'])
 require(set(producer)=={'Solidity.Frontend.ExecutableAst.Shared.'+n for n in ['Boundary','Compose','Intrinsic','Scope','Translate']}|{'Solidity.Frontend.ExecutableAst.ControlTuple.Adapter','Solidity.Frontend.ExecutableAst.Memory.Reader','Solidity.Tools.DirectRuntime'},'producer executable boundary set')
 for name,expected in [('native/direct-check',native['executable']),('direct/direct.wasm',wasm['wasm']),('direct/direct.js',wasm['javascript'])]:
  require(sha(runtime[name])==expected,'build/binary identity')
 def saved(name):return json.loads(evidence['amended-source/'+name])
 receipts=[]
 hashes={sha(raw):name for name,raw in evidence.items()}
 for gate in handoff['gates']:
  require(gate['sha256'] in hashes,'missing gate receipt')
  record=json.loads(evidence[hashes[gate['sha256']]])
  require(record['command']==gate['command'] and record['exitCode']==gate['exitCode'],'gate receipt drift')
  require(record['scope']=={'memoryMaxBytes':12884901888,'memorySwapMaxBytes':0},'recorded scope drift')
  require(record['minimumOuterHeadroomBytes']>=4294967296,'recorded headroom')
  receipts.append({'member':hashes[gate['sha256']],'command':record['command'],'exitCode':record['exitCode']})
 observations={}
 for family,count in [('box-controls',11),('diamond-controls',11),('A-controls',9),('B-controls-authenticated',84),('C-controls',14)]:
  observations[family]=parity(saved(family+'/control-inventory-with-guard.json'),count,wasm['wasm'])
 identity_keys={'identity.'+tag+'.'+mode for tag in ['box','diamond'] for mode in ['non-ir','ir']}
 identity_rows=[r for r in saved('B-controls-authenticated/control-inventory-with-guard.json')['native'] if r.get('caseKey') in identity_keys]
 require({r['caseKey'] for r in identity_rows}==identity_keys and all(r['reply']['results'][0]['status']=='proved' and r['reply']['results'][0]['tag']==r['caseKey'].split('.')[1] for r in identity_rows),'mandatory saved Identity modalities/modes')
 observations['functional83']=parity(saved('functional83/results.json'),83,wasm['wasm'])
 closure=saved('closure/summary.json');selected=saved('closure/selected-C-objects.json')
 require(closure['nativeSha256']==native['executable'] and closure['wasmSha256']==wasm['wasm'],'closure binary identity')
 require(len(selected)==len({r['module'] for r in selected})==closure['selectedModulesInventoried']==206,'selected inventory denominator')
 negative=saved('negative-controls/browser-control-completion.json')
 require(negative['binarySha256']==wasm['wasm'] and negative['passed'] is False and len(negative['failures'])==1,'retained browser failure')
 failure=negative['failures'][0]['record'];require(failure['name']=='invariantCountsToBound','unexpected retained failure')
 stack=failure['reply']['workerError']['stack'];layout=layout_tools.wasm_layout(runtime['direct/direct.wasm'])
 frames=layout_tools.frame_locations(stack,layout)
 return {'guardedRegression':'H77 fixed-byte recipient inspection cannot establish newer address or whole-goal qualification',
 'inputs':{n:{'path':str(paths[n]),'sha256':s} for n,s in PINS.items()},'ownerHead':HEAD,'sourceBuildHead':SOURCE,'producerHead':PRODUCER,
 'evidencePayloadsVerified':875,'runtimePayloadsVerified':5,'gitSourceModulesVerified':343,'producerExecutableBoundaryVerified':producer,'completeProducerTreeCompared':False,
 'nativeSha256':native['executable'],'wasmSha256':wasm['wasm'],'observations':observations,'savedGateReceipts':receipts,
 'mandatorySavedIdentityCases':sorted(identity_keys),'selectedInventoryRecords':206,'actualSelectedObjectBytesVerified':False,'retainedBrowserFailure':{'name':failure['name'],'message':failure['reply']['workerError']['message'],'framesWithinActualWasmBodies':len(frames)},
 'reportedCostStops':handoff['costStops'],'runtimeGatePass':False,'execution':False,'extraction':False,
 'boundary':'Independent archive/index/Git-source/binary-manifest and saved request/result consistency inspection only. Saved receiver observations were not rerun. No compiler/source preservation, actual object-code verification, universal closure, address qualification, repair, performance acceptance or whole-goal completion.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--directory',type=Path,default=DEFAULT);p.add_argument('--handoff',type=Path,default=HANDOFF);p.add_argument('--report',type=Path);a=p.parse_args()
 r=verify(a.directory,a.handoff);raw=json.dumps(r,indent=2)+'\n'
 if a.report:a.report.write_text(raw)
 else:print(raw,end='')
