"""Guards exact historical WASM symbol attribution without stale H90 qualification.
Reads authenticated maps/receipts/source only; never executes producer scripts or binaries.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,tarfile
ROOT=Path(__file__).resolve().parents[3];O=Path(__file__).resolve().parent
ARCHIVE=Path('/workspace/h62-coordinator-inputs/exact-stack-symbols-d43c81b85561.tar.gz')
ARCHIVE_SHA='d43c81b8556171d66356297a290464a9616d2650e183f2822468147b9ca43f1f'
WASM_SHA='6ae1d6db106102dc38725cb32cb1ba7996c537d1948b156d4acae1cd9139b563'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def symbol_table(raw,count):
 lines=raw.decode().splitlines();table={int(s.split(':',1)[0]):s.split(':',1)[1] for s in lines}
 assert len(lines)==len(table)==count and set(table)==set(range(count)),'symbol index domain'
 return table
def verify():
 assert ARCHIVE.stat().st_size==214639 and sha(ARCHIVE.read_bytes())==ARCHIVE_SHA
 with tarfile.open(ARCHIVE,'r:gz') as t:
  members=t.getmembers();assert len(members)==10 and all(m.isfile() for m in members)
  assert len({m.name for m in members})==10
  request=json.load(t.extractfile('delivery-request.json'));records=request['files']
  assert len(records)==9 and len({r['member'] for r in records})==9
  assert {m.name for m in members}=={'delivery-request.json'}|{r['member'] for r in records}
  data={}
  for r in records:
   raw=t.extractfile(r['member']).read();assert len(raw)==r['bytes'] and sha(raw)==r['sha256'];data[r['member']]=raw
  mapping=json.loads(data['mapping.json']);recovery=json.loads(data['h81-symbols-recovery.json']);gate=json.loads(data['h81-symbols-gate.json'])
  assert recovery['exitCode']==0 and recovery['output']==mapping
  assert mapping['historicalWasmSha256']==mapping['diagnosticWasmSha256']==request['historicalWasmSha256']==WASM_SHA
  assert mapping['exactWholeBinaryEqual'] is True and mapping['functionIndexDomainUnchanged'] is True
  assert mapping['frames']==request['frames']
  assert sha(data['direct.js.symbols'])==mapping['symbolMap']['sha256']
  assert mapping['symbolMap']['entries']==3939
  symbols=symbol_table(data['direct.js.symbols'],3939)
  assert '--emit-symbol-map' in json.loads(data['command.json'])
  historical=data['ReadBounds-historical.lean'];expected=subprocess.check_output(['git','show','0140eb13b2f122d421deb07a19575a6801b21dfc:Solidity/Calculus/ReadBounds.lean'],cwd=ROOT)
  assert historical==expected
  spec=importlib.util.spec_from_file_location('wasm_layout',O/'diagnose-native-evidence.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
  binary=(O/'artifacts/native-intake/.lake/native-browser-h81/direct/direct.wasm').read_bytes();assert sha(binary)==WASM_SHA
  layout=module.wasm_layout(binary);assert layout['imports']+len(layout['bodies'])==len(symbols)
  control=json.loads(data['browser-control-completion.json']);assert control['binarySha256']==WASM_SHA
  failure=next(r for r in control['requests'] if r['name']=='invariantCountsToBound')
  frames=module.frame_locations(failure['reply']['workerError']['stack'],layout)
  declared={r['index']:r['name'] for r in mapping['frames']};assert len(declared)==6 and set(declared)=={r['index'] for r in frames}
  for frame in frames:assert symbols[frame['index']]==declared[frame['index']]
 return {'regression':'Exact historical stack symbols without fresh-binary or causal-repair claims','archiveSha256':ARCHIVE_SHA,'pinnedMembers':9,'historicalWasmSha256':WASM_SHA,'symbolMapSha256':mapping['symbolMap']['sha256'],'symbolEntries':len(symbols),'mappedFrameOccurrences':len(frames),'frames':mapping['frames'],'sourcePath':'Solidity/Calculus/ReadBounds.lean','historicalSourceSha256':sha(historical),'currentSourceIdentical':historical==(ROOT/'Solidity/Calculus/ReadBounds.lean').read_bytes(),'recordedProducerGateExit':gate['exitCode'],'producerRecoveryExit':recovery['exitCode'],'producerReportsBitIdenticalRelink':True,'localRelinkOrBenchmarkExecuted':False,'independentRelinkByteComparison':False,'boundary':'Authenticated producer symbol/relink receipts and locally verified original WASM/map/source consistency. Relinked binary is not separately supplied; equality is producer-checked evidence, not a locally repeated relink comparison. Names locate fitsM bounds-check frames, not a proved root cause or algorithm repair. No957/H90freshness or runtime acceptance.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--report',type=Path);a=p.parse_args();r=verify()
 if a.report:a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps(r))
