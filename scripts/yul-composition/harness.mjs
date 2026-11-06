#!/usr/bin/env node
/** VY5 backfill. Compiler/reference evidence is never Lean correspondence. */
import {readFileSync,writeFileSync,mkdirSync,existsSync} from 'node:fs';
import {resolve,dirname,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {isDeepStrictEqual} from 'node:util';
import {capturedMachine,validateCapture,validateCallCapture} from './capture.mjs';
import {checkStateOracles,STATE_ORACLE_IDS,compareLocalState} from './oracles.mjs';
export {checkStateOracles} from './oracles.mjs';
import {parseFixture,withPreamble,evmCompatible,runtimePipelines} from '../solidity-upstream.mjs';
export const ROOT=resolve(dirname(fileURLToPath(import.meta.url)),'../..');
export const PIN='1835d247de183f23e7b0e2bc4a50732af525b77c';
export const COMPILER_SHA='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';
export const VERSION='0.8.38+commit.1835d247.Emscripten.clang';
export const sha=b=>createHash('sha256').update(b).digest('hex');
const json=p=>JSON.parse(readFileSync(p,'utf8'));
const encode=x=>JSON.stringify(x,null,2)+'\n';
function save(p,x) {mkdirSync(dirname(p),{recursive:true});writeFileSync(p,encode(x));}
export function checkedCompiler(path) {
  if(sha(readFileSync(path))!==COMPILER_SHA) throw Error('compiler SHA mismatch');
  const solc=createRequire(import.meta.url)(resolve(path));
  if(solc.cwrap('solidity_version','string',[])()!==VERSION) throw Error('compiler version mismatch');
  const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
  return input=>compile(JSON.stringify(input),0,0);
}
export function inputFor(sources,pipeline,optimized=false) {
  if(!['legacy','viaIR'].includes(pipeline)) throw Error('unknown pipeline');
  return {language:'Solidity',sources,settings:{viaIR:pipeline==='viaIR',evmVersion:'osaka',
    optimizer:{enabled:optimized,runs:200},metadata:{appendCBOR:false},
    outputSelection:{'*':{'':['ast'],'*':['abi','storageLayout','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers']}}}};
}
/** Advisory policy scan of actual solc AST only; not the lane VY1 importer. */
export function policyScan(ast) {
  if(!ast || ast.nodeType!=='SourceUnit' || !Array.isArray(ast.nodes)) throw Error('malformed source AST');
  const blocks=[],refusals=[];
  function walk(n,visit) { if(!n || typeof n!=='object') return;visit(n);
    for(const v of Object.values(n)) {if(Array.isArray(v)) v.forEach(x=>walk(x,visit));else if(v && typeof v==='object') walk(v,visit);} }
  walk(ast,n=>{if(n.nodeType!=='InlineAssembly') return;
    if(n.AST?.nodeType!=='YulBlock' || !Array.isArray(n.AST.statements)) throw Error('malformed Yul block');
    const calls=[];walk(n.AST,y=>{if(y.nodeType==='YulFunctionCall') calls.push(y.functionName?.name);});
    const flags=n.flags??[];
    if(!Array.isArray(flags)) throw Error('malformed flags');
    const reasons=[];
    for(const name of calls) if(['gas','msize','pc','codesize','codecopy','callcode'].includes(name)) reasons.push(name);
    if(!flags.includes('memory-safe')) reasons.push('non-memory-safe');
    // Canonical rethrow stays governed by the existing declaration-sensitive
    // memoryRethrow? importer. This preflight deliberately does not certify it.
    blocks.push({src:n.src,flags,calls,reasons,canonicalException:'not evaluated; existing importer owns declaration/shape checks'});
    refusals.push(...reasons);
  });
  return {kind:'advisory-only',blocks,refusals:[...new Set(refusals)],actualLeanImport:'pending'};
}
export function validateProvenance(record,input,raw) {
  if(record.compilerSha256!==COMPILER_SHA || record.compiler!==VERSION || record.commit!==PIN ||
    record.inputSha256!==sha(JSON.stringify(input)) || record.outputSha256!==sha(raw) ||
    JSON.stringify(record.settings)!==JSON.stringify(input.settings) ||
    record.pipeline!==(input.settings.viaIR?'viaIR':'legacy') || input.settings.evmVersion!=='osaka')
    throw Error('stale or mismatched compiler provenance');
  const expected=Object.fromEntries(Object.entries(input.sources).map(([n,v])=>[n,sha(v.content)]));
  if(JSON.stringify(record.sources)!==JSON.stringify(expected)) throw Error('source provenance mismatch');
}
export function compileRecord(compile,input,path) {
  const raw=compile(input); // preserve original compiler output before parsing
  const record={commit:PIN,compiler:VERSION,compilerSha256:COMPILER_SHA,
    pipeline:input.settings.viaIR?'viaIR':'legacy',settings:input.settings,
    sources:Object.fromEntries(Object.entries(input.sources).map(([n,v])=>[n,sha(v.content)])),
    inputSha256:sha(JSON.stringify(input)),outputSha256:sha(raw)};
  if(path) {save(path+'.input.json',input);writeFileSync(path+'.output.json',raw);save(path+'.provenance.json',record);}
  validateProvenance(record,input,raw);
  const output=JSON.parse(raw);
  return {record,output,errors:(output.errors??[]).filter(e=>e.severity==='error')};
}
/** Exact observations; absent fields are unresolved, never wildcards. */
export function compare(expected,actual) {
  if(!expected) return {status:'pending',reason:'no independent expected observation'};
  if(!['failed','returnData','logs'].every(k=>Object.hasOwn(expected,k)))
    return {status:'blocked',reason:'incomplete expected observation shape'};
  const differences=[];
  for(const [k,v] of Object.entries(expected)) {
    if(!Object.hasOwn(actual,k)) return {status:'blocked',reason:'missing observation: '+k};
    if(!isDeepStrictEqual(v,actual[k])) differences.push(k);
  }
  return {status:differences.length?'mismatch':'match',differences};
}
const CHILDREN=['Y01','Y01.02','Y02','Y03','Y04','Y05','Y06','Y07.01','Y07.02','Y08.01','Y08.02','Y09.01','Y09.02','Y09.03','G48','G49.01','G49.02','G49.03','G50.01','G50.02','G51.01','G51.02','G51.interface','Y10'];
const REQUIRED_ROWS={"Y01":{"owner":"VY1","dependencies":["S00"],"obligation":"Intrinsic scoped Yul AST; Osaka admission and canonical rethrow instance"},"Y01.02":{"owner":"VY1","dependencies":["Y01","G08","G09","G10","G11"],"obligation":"Checked Yul parsing over G08-G11 lexer"},"Y02":{"owner":"VY1","dependencies":["Y01","S01"],"obligation":"Scope/arity/literal/external-reference typing; checker soundness and completeness"},"Y03":{"owner":"VY1","dependencies":["Y02","S02","S03","V04"],"obligation":"Word/control/function semantics; horizon and dirty-bit embedding"},"Y04":{"owner":"VY2","dependencies":["Y03","S04","G27.01","G27.02","G27.03","G27.04","G27.05"],"obligation":"Packing/residual persistent/transient views, decode/encode, rollback and reset"},"Y05":{"owner":"VY2","dependencies":["Y03","S04","V04b","G32"],"obligation":"Byte memory, MemOK preservation and allocation refinement; G01 YQ3 amendment"},"Y06":{"owner":"VY2","dependencies":["Y05","S04.04"],"obligation":"Calldata copy/load/hash and universally quantified environment inputs"},"Y07.01":{"owner":"VY4","dependencies":["Y06","G22","G42","V13"],"obligation":"Raw call/staticcall/returndata/create/create2 correctness"},"Y07.02":{"owner":"VY4","dependencies":["Y07.01","G42","V13"],"obligation":"Delegatecall/EIP-6780/logs and Solidity emit; G01 YQ6 amendment"},"Y08.01":{"owner":"VY3","dependencies":["Y04","Y05","Y06","G24","G27","G32","V12"],"obligation":"Concrete compiler stack/frame relation against G24 and Y04/Y05"},"Y08.02":{"owner":"VY3","dependencies":["Y08.01","G45","G46","V15"],"obligation":"Actual opcode and bytecode correspondence through G45/G46/Bridge"},"Y09.01":{"owner":"VY1","dependencies":["Y03","G51.interface"],"obligation":"Sound word/control calculus; printed rules and Lean-only map rows"},"Y09.02":{"owner":"VY2","dependencies":["Y04","Y05","Y06","G51.interface"],"obligation":"Sound physical/input calculus; update laws and printed rules"},"Y09.03":{"owner":"VY4","dependencies":["Y07.01","Y07.02","G51.interface"],"obligation":"Sound world-effect calculus and log observations"},"G48":{"owner":"V16","dependencies":["Y01","Y02","Y03","Y04","Y05","Y06","Y07.01","Y07.02","Y08.01"],"obligation":"Concrete accepted source coverage and lowering; no residual assembly restriction"},"G49.01":{"owner":"V16","dependencies":["G48","Y08.01"],"obligation":"Every assembly constructor compiled with actual pass certificates"},"G49.02":{"owner":"V16","dependencies":["G49.01","Y08.02"],"obligation":"Runtime source-to-bytes simulation in both pipelines"},"G49.03":{"owner":"V16","dependencies":["G49.02"],"obligation":"Nonvacuity, failure preservation and resource-indexed progress"},"G50.01":{"owner":"V16","dependencies":["G49.02","Y07.01"],"obligation":"Constructor/initcode/runtime installation and failure observations"},"G50.02":{"owner":"V16","dependencies":["G50.01","Y07.02"],"obligation":"Reachable transaction/world composition and adversarial quantification"},"G51.01":{"owner":"V16","dependencies":["Y09.01","Y09.02","Y09.03"],"obligation":"Affected calculus soundness"},"G51.02":{"owner":"V16","dependencies":["G49.03","G50.02","G51.01"],"obligation":"Box/diamond/spec/callback/loop transfer"},"G51.interface":{"owner":"V16","dependencies":["V16"],"obligation":"Actual G51 rule/specification interface contracts consumed by Y09; distinct from completed G51.01 theorem"},"Y10":{"owner":"VY5","dependencies":["G48","G49.01","G49.02","G49.03","G50.01","G50.02","G51.01","G51.02","Y08.02","Y07.02"],"obligation":"Concrete joint assembly composition and import closure"}};
const REQUIRED_COMBOS={"loops":{"constructors":["assembly","forStmt","whileStmt","doWhile","breakStmt","continueStmt"],"dependencies":["Y03","Y09.01","G49.03","G51.02"],"fixture":"loops"},"modifiers":{"constructors":["assembly","modifier","modInv"],"dependencies":["Y03","G48","G49.01"],"fixture":"modifiers"},"try-catch":{"constructors":["assembly","tryStmt","catchPlain","catchSig"],"dependencies":["Y07.01","Y07.02","G49.02"],"fixture":"try-catch"},"unchecked":{"constructors":["assembly","uncheckedItem"],"dependencies":["Y03","Y09.01","G48"],"fixture":"unchecked"},"constructors":{"constructors":["assembly","constructor","new"],"dependencies":["Y07.01","G50.01"],"fixture":"constructors"},"libraries":{"constructors":["assembly","library","call"],"dependencies":["Y08.01","Y07.02","G48"],"fixture":"libraries"}};
const COMBINATIONS=['loops','modifiers','try-catch','unchecked','constructors','libraries'];
/** This tree has no actual VY correctness interfaces. Reject invented closure. */
export function checkProofControls(registration) {
  if(registration.schema!==1 || registration.file!=='tests/yul-composition/RethrowControls.lean' || registration.assemblyObligationsClosed?.length!==0) throw Error('proof-control scope drift');
  const bytes=readFileSync(join(ROOT,registration.file));
  if(sha(bytes)!==registration.sourceSha256) throw Error('stale control proof source');
  if(registration.dependency?.file!=='Solidity/Frontend/SolcJson/Body.lean' || sha(readFileSync(join(ROOT,registration.dependency.file)))!==registration.dependency.sha256) throw Error('stale recognizer dependency');
  const text=bytes.toString('utf8');
  const actual=[...text.matchAll(/theorem (\w+)\s*:\s*([\s\S]*?) := by rfl/g)].map(([,name,signature])=>({declaration:'Solidity.Yul.Composition.RethrowControls.'+name,signature:signature.split(/\s+/).join(' ').trim(),kind:'finite-recognizer-refusal'}));
  const names=['extra_statement','different_names','malformed'].map(n=>'Solidity.Yul.Composition.RethrowControls.'+n);
  if(!isDeepStrictEqual(actual,registration.proofs) || !isDeepStrictEqual(actual.map(r=>r.declaration),names) || registration.runtimeGuards!==7 || [...text.matchAll(/^#guard /gm)].length!==7) throw Error('missing/stale proof or runtime control');
  return {finiteProofs:actual.length,runtimeGuards:7,assemblyObligationsClosed:0,kernelGate:'separate required gate'};
}
export function checkLedger(ledger,fixtures) {
  if(ledger.schema!==1 || ledger.base!=='0b078cefaf7daad79007b87b72df64eb6936420f' ||
    ledger.parent!=='docs/feature-work/roadmap-g03-ledger.json' || ledger.feature!=='inlineAssembly') throw Error('ledger identity drift');
  const ids=ledger.obligations.map(r=>r.id), combos=ledger.combinations.map(r=>r.id);
  if(JSON.stringify([...ids].sort())!==JSON.stringify([...CHILDREN].sort()) ||
    JSON.stringify([...combos].sort())!==JSON.stringify([...COMBINATIONS].sort())) throw Error('missing/duplicate/unknown obligation');
  for(const row of ledger.obligations) for(const [key,value] of Object.entries(REQUIRED_ROWS[row.id]))
    if(JSON.stringify(row[key])!==JSON.stringify(value)) throw Error('dependency/owner/obligation drift');
  for(const row of ledger.combinations) for(const [key,value] of Object.entries(REQUIRED_COMBOS[row.id]))
    if(JSON.stringify(row[key])!==JSON.stringify(value)) throw Error('combination dependency drift');
  for(const row of [...ledger.obligations,...ledger.combinations]) {
    if(row.status!=='pending' || row.proof!==null) throw Error('missing concrete proof interfaces: closure/stale proof rejected');
    if(!row.dependencies.length || row.dependencies.some(d=>typeof d!=='string')) throw Error('missing dependency');
  }
  const ctorText=readFileSync(join(ROOT,'Solidity/Source/Ctor.lean'),'utf8').match(/inductive Ctor where([\s\S]*?)deriving/)[1];
  const ctors=new Set(ctorText.match(/[A-Za-z]\w*/g));
  for(const row of ledger.combinations) {
    if(row.constructors.some(c=>!ctors.has(c))) throw Error('unknown source constructor');
    if(!row.dependencies.every(d=>ids.includes(d)) || !row.constructors.length ||
       !fixtures.some(f=>f.id===row.fixture && f.expected)) throw Error('combination coverage missing');
  }
  return {obligations:ids.length,combinations:combos.length,closed:0,proofGate:'pending'};
}
export function checkException(exception,stage='runtime') {
  if(exception && !['revert','out of gas','stack overflow'].includes(exception)) throw Error('unadapted '+stage+' exception: '+exception);
  return exception;
}
export function diagnosticsMatch(errors,expected) {
  return isDeepStrictEqual(errors.map(e=>({type:e.type,code:e.errorCode,message:e.message})),expected);
}
/** Reference engine only. No source-state/target relation is asserted. */
export async function execute(artifact,fixture) {
  const {hexToBytes,bytesToHex}=await import('../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js');
  const {vm,observer}=await capturedMachine();let transaction=0;
  const call=options=>observer.run(options,++transaction);
  const deployment=await call({data:hexToBytes('0x'+artifact.evm.bytecode.object)});
  const address=deployment.result.createdAddress;
  if(fixture.deploymentOnly) {
    const e=deployment.result.execResult;
    const exception=e.exceptionError?.error??null;
    checkException(exception,'deployment');
    const record={phase:'deployment',executionKind:'runCall',deployment:{candidateAddress:address?.toString()??null,runtimeInstalled:false},deploymentCapture:deployment.capture,observed:{capture:deployment.capture,metrics:deployment.metrics,failed:!!e.exceptionError,exception,returnData:bytesToHex(e.returnValue),logs:(e.logs??[]).map(([emitter,topics,data])=>({emitter:bytesToHex(emitter),topics:topics.map(bytesToHex),data:bytesToHex(data)}))}};
    return {...record,stateComparison:compareLocalState(fixture,record)};
  }
  if(deployment.result.execResult.exceptionError || !address) throw Error('reference deployment failed');
  const installed=bytesToHex(await vm.evm.stateManager.getCode(address));
  if(installed!=='0x'+artifact.evm.deployedBytecode.object) throw Error('runtime installation bytes differ');
  let targetMutation=null;
  if(fixture.targetMutation) {
    const mutants={'always-revert':'0x5f5ffd','incorrect-opcode':'0x60016029035f5260205ff3'};
    const mutantRuntime=mutants[fixture.targetMutation];
    if(!mutantRuntime) throw Error('unsupported target mutation');
    const referenceRuntime=fixture.targetMutation==='incorrect-opcode'?'0x60016029015f5260205ff3':installed;
    await vm.evm.stateManager.putCode(address,hexToBytes(referenceRuntime));
    if(bytesToHex(await vm.evm.stateManager.getCode(address))!==referenceRuntime) throw Error('reference target read-back differs');
    const preview=await call({to:address,data:hexToBytes('0x'+artifact.evm.methodIdentifiers[fixture.signature]+fixture.args.join(''))});
    const pe=preview.result.execResult;
    const previewObservation={failed:!!pe.exceptionError,exception:checkException(pe.exceptionError?.error??null),returnData:bytesToHex(pe.returnValue),logs:(pe.logs??[]).map(([emitter,topics,data])=>({emitter:bytesToHex(emitter),topics:topics.map(bytesToHex),data:bytesToHex(data)}))};
    if(compare(fixture.expected,previewObservation).status!=='match') throw Error('unmutated reference target did not match');
    await vm.evm.stateManager.putCode(address,hexToBytes(mutantRuntime));
    if(bytesToHex(await vm.evm.stateManager.getCode(address))!==mutantRuntime) throw Error('target mutation read-back differs');
    targetMutation={kind:'deliberately-mutated-target-reference',mutationName:fixture.targetMutation,referenceRuntime,referenceObservation:previewObservation,originalRuntime:installed,originalRuntimeSha256:sha(hexToBytes(installed)),mutantRuntime,mutantRuntimeSha256:sha(hexToBytes(mutantRuntime))};
  }
  const selector=artifact.evm.methodIdentifiers[fixture.signature];
  if(!selector) throw Error('missing method identifier');
  const {result,metrics,capture}=await call({to:address,data:hexToBytes('0x'+selector+fixture.args.join(''))});
  const e=result.execResult,exception=e.exceptionError?.error??null;
  checkException(exception);
  const observed={failed:exception!==null,returnData:bytesToHex(e.returnValue),logs:(e.logs??[]).map(([emitter,topics,data])=>({emitter:bytesToHex(emitter)===address.toString()?'self':bytesToHex(emitter),topics:topics.map(bytesToHex),data:bytesToHex(data)})),exception,metrics,
    capture,worldScope:'All API-touched accounts/slots captured; independent comparisons only for explicit controlled oracles, no untouched-world equivalence',
    memoryScope:'Frame-indexed raw final memory and before-LOG/RETURN/REVERT snapshots; only specified semantic regions compared'};
  observed.rawLogs=(e.logs??[]).map(([emitter,topics,data])=>({emitter:bytesToHex(emitter),topics:topics.map(bytesToHex),data:bytesToHex(data)}));
  observed.storage={};
  for(const [slot,value]of Object.entries(capture.post[address.toString()]?.persistent??{}))observed.storage[BigInt(slot).toString()]=value;
  const record={phase:'runtime',executionKind:'runCall',deploymentCapture:deployment.capture,deployment:{address:address.toString(),runtimeSha256:sha(deployment.result.execResult.returnValue),metrics:deployment.metrics},targetMutation,observed};
  return {...record,stateComparison:compareLocalState(fixture,record)};
}
const LOCAL_IDS=["loops", "modifiers", "try-catch", "unchecked", "constructors", "libraries", "always-revert", "incorrect-opcode", "compiler-dependent", "non-memory-safe", "unsupported-callcode", "dirty-bits", "allocation", "memory-storage-logs", "malformed-import", "constructor-failure", "dirty-bits-cleaned", "try-body", "try-error", "try-bytes", "try-panic", "mixed-logs", "new-constructor", "always-revert-target"];
const LOCAL_POSITIVE=["loops", "modifiers", "try-catch", "unchecked", "constructors", "libraries", "always-revert", "non-memory-safe", "dirty-bits", "memory-storage-logs", "constructor-failure", "dirty-bits-cleaned", "try-body", "try-error", "try-bytes", "try-panic", "mixed-logs", "new-constructor"];
const LOCAL_POLICY=["compiler-dependent", "non-memory-safe", "unsupported-callcode"];
export function localMatrixFailures(results,profiles) {
  const failures=[];
  const ids=LOCAL_IDS;
  for(const {pipeline,optimized} of profiles) for(const id of ids) {
    const rows=results.filter(r=>r.kind==='combination' && r.id===id && r.pipeline===pipeline && r.optimized===optimized);
    const label=id+'/'+pipeline+'/'+optimized;
    if(rows.length!==1) {failures.push(label+': missing/duplicate local control');continue;}
    const r=rows[0];
    if(LOCAL_POSITIVE.includes(id) && (r.status!=='match' || r.comparison?.differences?.length!==0)) failures.push(label+': required observation did not match');
    if(LOCAL_POLICY.includes(id) && (r.compilerStatus!=='compiled' || r.policyCheck!=='match')) failures.push(label+': policy control not established');
    if(id==='malformed-import' && (r.compilerStatus!=='rejected' || r.compilerControl!=='match')) failures.push(label+': precise import refusal not established');
    if(id==='incorrect-opcode' && (r.targetMutation?.mutantRuntime!=='0x60016029035f5260205ff3' || r.status!=='mismatch' || JSON.stringify(r.comparison?.differences)!==JSON.stringify(['returnData']))) failures.push(label+': opcode control not established');
    if(id==='always-revert-target' && (r.status!=='mismatch' || r.observed?.exception!=='revert' || r.targetMutation?.mutantRuntime!=='0x5f5ffd' || JSON.stringify(r.comparison?.differences)!==JSON.stringify(['failed','returnData','exception']))) failures.push(label+': always-revert target control not established');
    if(id==='allocation' && (r.compilerStatus!=='compiled' || r.layoutSanity!==true || r.observed?.exception!==null || r.observed?.failed!==false || r.observed?.logs?.length!==0 || !/^0x[0-9a-f]{64}$/i.test(r.observed?.returnData??''))) failures.push(label+': allocation observation not established');
  }
  return failures;
}
export function controlFailures(results,requireExecution=false) {
  const failures=[];
  if(requireExecution) for(const pipeline of ['legacy','viaIR'])
    if(!results.some(r=>r.id==='incorrect-opcode' && r.pipeline===pipeline)) failures.push('missing incorrect-opcode '+pipeline);
  for(const r of results) {
    if(r.stateComparison&&['mismatch','blocked'].includes(r.stateComparison.status))failures.push(r.id+': state oracle did not match');
    if(requireExecution&&STATE_ORACLE_IDS.includes(r.id)) {
      const fixture=json(join(ROOT,'tests/yul-composition/fixtures.json')).find(f=>f.id===r.id);
      const comparison=compareLocalState(fixture,r);
      if(comparison.status!=='match'||!isDeepStrictEqual(comparison,r.stateComparison))failures.push(r.id+': missing/stale required state comparison');
    }
    if(requireExecution&&r.kind==='combination'&&[...LOCAL_POSITIVE,'incorrect-opcode','always-revert-target','allocation'].includes(r.id)&&!r.observed?.capture)failures.push(r.id+': missing required capture');
    if(requireExecution&&r.observed)try{validateCallCapture(r.observed.capture,r.observed);validateCapture(r.deploymentCapture);}catch(e){failures.push(r.id+': missing/malformed capture: '+e.message);}
    if(r.layoutSanity===false) failures.push(r.id+': invalid reference allocation layout');
    if(r.policyCheck==='mismatch' || r.compilerControl==='mismatch') failures.push(r.id+': control mismatch');
    if(r.reference?.validationFailure) failures.push(r.id+': malformed upstream evidence: '+r.reference.validationFailure);
    if(r.reference?.status==='broken') failures.push(r.id+': upstream reference mismatch');
    if(r.status==='mismatch' && !['must-mismatch','must-reject-always-revert'].includes(r.negativeControl)) failures.push(r.id+': observation mismatch');
    if(requireExecution && r.id==='incorrect-opcode' &&
       (r.status!=='mismatch' || JSON.stringify(r.comparison?.differences)!==JSON.stringify(['returnData'])))
      failures.push(r.id+': incorrect-opcode control did not distinguish bytes');
  }
  return failures;
}
export async function run({compiler,out,corpus,executeReference=false,optimizerAlso=false,compile=checkedCompiler(compiler)}) {
  mkdirSync(out,{recursive:true});
  const fixtures=json(join(ROOT,'tests/yul-composition/fixtures.json'));
  const ledger=checkLedger(json(join(ROOT,'tests/yul-composition/ledger.json')),fixtures);
  const proofControls=checkProofControls(json(join(ROOT,'tests/yul-composition/proof-controls.json')));
  const results=[];
  // These are both-pipeline probes. Upstream-required modes are retained
  // separately; an out-of-profile probe never rewrites an upstream verdict.
  const jobs=fixtures.map(f=>({...f,kind:'combination',sources:{'case.sol':{content:f.source}},requiredPipelines:['legacy','viaIR']}));
  if(corpus) {
    const inv=json(join(corpus,'inventory.json'));
    if(inv.commit!==PIN || inv.archiveSha256!=='9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d') throw Error('inventory pin mismatch');
    if(inv.snapshotSha256!==sha(readFileSync(join(ROOT,'tests/upstream/snapshot.json')))) throw Error('snapshot provenance drift');
    const pinned=json(join(ROOT,'tests/upstream/snapshot.json')).files.filter(f=>f.path.startsWith('test/libsolidity/semanticTests/inlineAssembly/'));
    if(JSON.stringify(inv.files)!==JSON.stringify(pinned)) throw Error('inventory coverage drift');
    for(const row of inv.files) {
      const bytes=readFileSync(join(corpus,row.path));
      if(bytes.length!==row.bytes || sha(bytes)!==row.sha256) throw Error('fixture provenance drift');
      try {
        const parsed=parseFixture(new TextDecoder('utf-8',{fatal:true}).decode(bytes));
        jobs.push({id:row.path.split('/').at(-1),kind:'upstream',path:row.path,fixtureSha256:row.sha256,
          sources:Object.fromEntries([...parsed.sources].map(([n,s])=>[n,{content:withPreamble(s)}])),
          settings:parsed.settings,expectations:parsed.expectations,requiredPipelines:runtimePipelines(parsed.settings),
          osakaCompatible:(()=>{try{return evmCompatible(parsed.settings.EVMVersion);}catch{return null;}})(),parsed});
      } catch(e) {results.push({id:row.path,status:'blocked',reason:e.message,leanCorrespondence:'pending'});}
    }
  }
  for(const job of jobs) for(const pipeline of ['legacy','viaIR']) for(const optimized of (optimizerAlso?[false,true]:[false])) {
    const row={id:job.id,kind:job.kind,pipeline,optimized,required:job.requiredPipelines.includes(pipeline),
      originalSettings:job.settings,originalExpectations:job.expectations,osakaCompatible:job.osakaCompatible,
      expectedObservation:job.expected,expectedDiagnostics:job.expectedDiagnostics,fixtureSha256:job.fixtureSha256,negativeControl:job.negativeControl,leanCorrespondence:'pending',composition:'pending'};
    try {
      const input=inputFor(job.sources,pipeline,optimized),stem=join(out,job.kind+'-'+job.id+'-'+pipeline+(optimized?'-optimized':''));
      const {record,output,errors}=compileRecord(compile,input,stem);
      row.provenance=record;row.errors=errors;row.compilerStatus=errors.length?'rejected':'compiled';
      row.policy=Object.values(output.sources??{}).map(s=>policyScan(s.ast));
      row.policyCheck=job.policy?.startsWith('refuse:') ?
        (row.policy.some(p=>p.refusals.includes(job.policy.slice(7)))?'match':'mismatch'):'not-certified';
      if(job.compilerError) row.compilerControl=diagnosticsMatch(errors,job.expectedDiagnostics)?'match':'mismatch';
      if(errors.length) {row.status=job.compilerError?'reference-rejection-match':'blocked';row.reason='compiler rejected probe; original diagnostics retained';}
      else if(job.kind==='combination' && executeReference && job.expected) {
        const artifact=output.contracts['case.sol'].C;
        Object.assign(row,await execute(artifact,job));
        row.comparison=compare(job.expected,row.observed);
        row.status=row.comparison.status;
        row.negativeControl=job.negativeControl;
      } else {row.status='pending';row.reason='compile evidence only; runtime expectation/adapter pending';}
      if(job.allocationLayout && !errors.length && executeReference) {
        Object.assign(row,await execute(output.contracts['case.sol'].C,job));
        const ptr=BigInt(row.observed.returnData);
        row.layoutSanity=ptr>=128n && ptr%32n===0n;
        row.status='pending';row.reason='reference pointer retained; source allocation refinement pending';
      }
      // Upstream byte-vector wrapper reuses the shared bounded engine unchanged.
      if(job.kind==='upstream' && executeReference) {
        const {runFixture,validateFixtureEvidence}=await import('./upstream.mjs');
        // runFixture retains exactly the upstream-required pipelines/settings;
        // save once rather than presenting probe modes as upstream matches.
        if(pipeline==='legacy' && !optimized) {
          let referenceIndex=0;
          row.reference=await runFixture(job.path,corpus,i=>compileRecord(compile,i,stem+'.reference-'+referenceIndex++).output,policyScan);
          try { validateFixtureEvidence(row.reference,corpus); } catch(e) { row.reference.validationFailure=e.message; }
          save(stem+'.reference.json',row.reference);
        }
      }
    } catch(e) {row.status='blocked';row.reason=e.message;}
    results.push(row);save(join(out,'results.partial.json'),results);
  }
  const report={schema:1,scope:'External compiler/EVM evidence only. No Lean importer, source correspondence or composition proof.',
    ledger,proofControls,runnerSha256:sha(readFileSync(fileURLToPath(import.meta.url))),
    fixturesSha256:sha(readFileSync(join(ROOT,'tests/yul-composition/fixtures.json'))),
    adapterSha256:sha(readFileSync(join(ROOT,'scripts/solidity-upstream.mjs'))),
    upstreamWrapperSha256:sha(readFileSync(join(ROOT,'scripts/yul-composition/upstream.mjs'))),
    oracleModuleSha256:sha(readFileSync(join(ROOT,'scripts/yul-composition/oracles.mjs'))),upstreamStateOraclesSha256:sha(readFileSync(join(ROOT,'tests/yul-composition/upstream-state-oracles.json'))),
    stateOraclesSha256:sha(readFileSync(join(ROOT,'tests/yul-composition/state-oracles.json'))),captureSha256:sha(readFileSync(join(ROOT,'scripts/yul-composition/capture.mjs'))),
    referenceEngineSha256:sha(readFileSync(join(ROOT,'scripts/evm-reference/replay.mjs'))),
    referenceHost:{engine:'@ethereumjs/evm 10.1.3',hardfork:'osaka',initialGas:'100000000',stepLimit:5000000,allowUnlimitedContractSize:true,allowUnlimitedInitCodeSize:true},
    referenceLockSha256:sha(readFileSync(join(ROOT,'scripts/evm-reference/package-lock.json'))),results};
  save(join(out,'report.json'),report);return report;
}
if(process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  const args=process.argv.slice(2),o={};
  for(let i=0;i<args.length;i++) {const a=args[i];if(a==='--execute-reference') o.executeReference=true;
    else if(a==='--optimizer-also') o.optimizerAlso=true;
    else if(['--compiler','--out','--corpus'].includes(a) && args[i+1]) o[a.slice(2)]=resolve(args[++i]);else throw Error('unknown/missing argument: '+a);}
  if(!o.compiler || !o.out) throw Error('--compiler and --out required');
  const report=await run(o);
  const counts={};for(const r of report.results) counts[r.status]=(counts[r.status]??0)+1;
  console.log(JSON.stringify({counts,proofGate:'pending'}));
  // Full-lane completion is deliberately not encoded by this backfill command.
  const profiles=['legacy','viaIR'].flatMap(pipeline=>(o.optimizerAlso?[false,true]:[false]).map(optimized=>({pipeline,optimized})));
  const failures=[...controlFailures(report.results,o.executeReference),...(o.executeReference?localMatrixFailures(report.results,profiles):[])];
  if(failures.length) console.error(JSON.stringify(failures));
  process.exitCode=failures.length?1:0;
}
