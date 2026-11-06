"""Compare the unchanged native producer build against saved public API observations."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
owned=Path(__file__).resolve().parent;root=owned.parents[2];out=owned/'artifacts/native-3ad';binary=out/'direct-check'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
manifest=json.loads((out/'build.json').read_text());assert sha(binary)==manifest['executable']
assert manifest['leanCommit']=='797c613eb9b6d4ec95db23e3e00af9ac6657f24b'
for row in manifest['sourceFiles']:
 assert sha(root/(row['module'].replace('.','/')+'.lean'))==row['sourceSha256']
 assert sha(root/'.lake/build/ir'/(row['module'].replace('.','/')+'.c'))==row['cSha256']
source=owned/'artifacts/lean-source-797c613'
assert subprocess.check_output(['git','-C',str(source),'rev-parse','HEAD'],text=True).strip()==manifest['leanCommit']
assert not subprocess.check_output(['git','-C',str(source),'status','--porcelain'],text=True)
requests=[];expected=[];anchors=[]
for fixtureName,observationsName,modal in [('ComposedReaders.ast.json','direct-result-observations.json',False),('ModalityControls.ast.json','modality-observations.json',True)]:
 fixture=owned/'artifacts/h68-bulk'/fixtureName;ast=json.loads(fixture.read_text())['ast'];contract=next(n for n in ast['nodes'] if n.get('nodeType')=='ContractDefinition')
 observations=json.loads((owned/observationsName).read_text())
 for observation in observations:
  row=observation['checker'] if modal else observation
  requests.append(json.dumps({'contract':contract,'function':row['function'],'sourceId':row['sourceId']},separators=(',',':')))
  expected.append(row);anchors.append({'fixture':fixtureName,'fixtureSha256':sha(fixture),'function':row['function'],'sourceId':row['sourceId']})
assert len(expected)==18
unknown=json.loads((owned/'artifacts/h68-bulk/ModalityControls.ast.json').read_text())['ast']['nodes']
unknown=next(n for n in unknown if n.get('nodeType')=='ContractDefinition');unknown['nodeType']='UnknownCompilerNode'
requests.extend(['{broken',json.dumps({'contract':unknown})])
run=out/'empty-runtime-cwd';run.mkdir(exist_ok=True)
trace=out/'runtime.strace';env=dict(os.environ)
for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:env.pop(key,None)
payload='\n'.join(requests)+'\n'
(out/'runtime.requests.jsonl').write_text(payload)
(out/'expected-api-results.json').write_text(json.dumps(expected,indent=2)+'\n')
start=time.monotonic()
process=subprocess.run(['strace','-f','-e','trace=file,process,network','-o',str(trace),str(binary)],input=payload,text=True,capture_output=True,cwd=run,env=env)
executionWall=time.monotonic()-start
(out/'runtime.stdout').write_text(process.stdout);(out/'runtime.stderr').write_text(process.stderr)
assert process.returncode==0,(process.returncode,process.stderr)
lines=process.stdout.splitlines();assert json.loads(lines[0])=={'ready':True} and len(lines)==21
actual=[json.loads(line) for line in lines[1:]]
for i,row in enumerate(expected):assert actual[i]=={'results':[row]},(anchors[i],actual[i],row)
for row in actual[18:]:assert isinstance(row.get('gap'),str) and 'results' not in row
traceText=trace.read_text();assert not re.search(r'\.(?:olean|ilean|lean)(?:["/ ]|$)',traceText)
execs=re.findall(r'execve\("([^"]+)"',traceText);assert execs==[str(binary)],execs
assert not re.search(r'\b(?:socket|connect|sendto|recvfrom)\(',traceText)
ldd=subprocess.check_output(['ldd',str(binary)],text=True);(out/'ldd.txt').write_text(ldd)
assert not re.search(r'lib(?:Lean|leanshared|Lake|leancpp)',ldd)
symbols=subprocess.check_output(['nm','-S','--defined-only',str(binary)],text=True);(out/'symbols.txt').write_text(symbols)
frontend=[line for line in symbols.splitlines() if re.search(r'Lean_(?:Elab|Meta|Parser|Environment|Kernel|Compiler|Server|Widget)',line)]
for prefix in ['lean_expr_','lean_mk_app','lean_mk_lambda','lean_mk_pi','lean_mk_sort','l_Lean_Expr_', 'lean_environment_','lean_kernel_','lean_import_modules','l_Lean_Environment_','l_Lean_Kernel_']:
 assert not any(line.split()[-1].startswith(prefix) for line in symbols.splitlines()),prefix
assert 'solidity_direct_check' in symbols and 'l_Solidity_Frontend_ExecutableAst_Shared_executable' in symbols
result={'status':'native-functional-parity-pass; exhaustive binary closure not established','binary':str(binary),'binarySha256':sha(binary),'binaryBytes':binary.stat().st_size,'buildManifest':str(out/'build.json'),'buildManifestSha256':sha(out/'build.json'),'pinnedLeanSourceClean':True,'fixtureComparisons':len(expected),'failClosedRequests':2,'anchors':anchors,'runtimeExit':process.returncode,'runtimeWallSeconds':executionWall,'controlWallSeconds':time.monotonic()-start,'runtimeCwd':str(run),'serializedEnvironmentAccessObserved':False,'externalExecs':execs,'networkSyscallsObserved':False,'dynamicLeanFrontendLibraryObserved':False,'frontendOriginSymbolCandidates':frontend,'frontendOriginReview':str(owned/'evidence/adoption-3ad/frontend-origin/inventory.json'),'trace':str(trace),'traceSha256':sha(trace),'stdoutSha256':sha(out/'runtime.stdout'),'stderrSha256':sha(out/'runtime.stderr'),'boundary':'18 exact native-vs-saved-Lean-harness observations plus 2 fail-closed requests. Runtime trace shows no serialized Lean environment access or external frontend executable/library in these runs. The 14 frontend-origin candidates were independently classified as generic helpers/empty initializers; this does not establish exhaustive binary closure. No WASM,source preservation,universal backend adequacy or full migration claim.'}
(out/'controls.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'binarySha256':result['binarySha256'],'comparisons':18,'failClosedRequests':2,'frontendOriginSymbolCandidates':len(frontend),'runtimeExit':0,'runtimeWallSeconds':result['runtimeWallSeconds']}))
