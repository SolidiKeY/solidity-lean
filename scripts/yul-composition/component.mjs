#!/usr/bin/env node
/** Actual component executions; selected finite projections, never adequacy. */
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {isDeepStrictEqual as equal} from 'node:util';
import {ROOT,sha,checkedCompiler,inputFor,compileRecord,checkException,checkLedger,validateProvenance} from './harness.mjs';
import {keccak_256} from '../evm-reference/node_modules/@noble/hashes/sha3.js';
import {predictedAliases,LOCAL_CALLER} from './oracles.mjs';
import {capturedMachine,validateCapture,validateCallCapture} from './capture.mjs';
import {hexToBytes,bytesToHex} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
const PRODUCER_SHA='8ef05f37eee1ed003d13303bde83466330e9550cb2b423d80398be53f4c0733f';
const V16_SHA='bb38a3c924178c670426c93ab4053d5b07c940b3d8fc6b50592a636b63d60b16';
const SOURCE_SHA='d7a8103219a77a219500941d326ad8ace8f52cf150c78b4f91cfab279b4c1076';
const SCOPE='Finite actual component/encoded-target/solc projections; no universal source, compiler, raw-memory or whole-world correspondence.';
const expected={schema:1,rawWord:511,word:[259,99],scope:[7,259,99],repeat:[253,99],code:[96,9,96,250,1],revert:[0,7,1,238,171,205,238,1],success:[1,42,2,238,171,205,238,1]};
const observed=r=>({failed:!!r.result.execResult.exceptionError,exception:checkException(r.result.execResult.exceptionError?.error??null),returnData:bytesToHex(r.result.execResult.returnValue),logs:(r.result.execResult.logs??[]).map(([a,t,d])=>({emitter:bytesToHex(a),topics:t.map(bytesToHex),data:bytesToHex(d)})),metrics:r.metrics});
const word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
function bindCapture(c,actual,expected) {
 validateCallCapture(c,actual,{caller:LOCAL_CALLER,value:'0',...expected});
 const root=c.frames[0];if(root.caller!==LOCAL_CALLER||root.value!=='0'||root.input!==c.request.input||expected.to!==null&&(root.address!==expected.to||root.codeAddress!==expected.to))throw Error('root frame identity mismatch');return c;
}
export function validateLean(value) {
 if(!equal(value,expected))throw Error('missing/malformed/wrong component execution');return value;
}
export function verifyProducerReceipt(bytes) {
 if(sha(bytes)!==PRODUCER_SHA)throw Error('producer registry identity drift');return JSON.parse(bytes);
}
export function validateComponentLedger(record) {
 const original=JSON.parse(readFileSync(join(ROOT,'tests/yul-composition/ledger.json')));
 checkLedger(original,JSON.parse(readFileSync(join(ROOT,'tests/yul-composition/fixtures.json'))));
 if(original.componentEvidence!=='tests/yul-composition/component-ledger.json'||record.schema!==1||record.fullObligationsClosed!==0||record.originalObligations!==24||record.originalCombinations!==6||record.facts?.length!==13)throw Error('component ledger scope/coverage drift');
 const names=['revert_copy','copied_window_and_frame','caught_then_success','nested_revert_window','literalSum_run','repeat_increment_run','Controls.reverted_witness','Controls.success_witness','computed_outer_write','computed_outer_read','world_target_word','target_world_word','world_word_add'].map(n=>'Solidity.Yul.Composition.'+n);
 if(!equal(record.facts.map(f=>f.name).sort(),names.sort()))throw Error('missing/duplicate component proof');
 for(const f of record.facts){const short=f.name.slice('Solidity.Yul.Composition.'.length),module=short.startsWith('Controls.')?'Controls':['world_target_word','target_world_word','world_word_add'].includes(short)?'WordBridge':short==='repeat_increment_run'?'TargetRepeat':short.startsWith('computed_outer_')?'ScopeTransport':'Concrete';if(f.module!=='Solidity/Yul/Composition/'+module+'.lean')throw Error('wrong component proof module');}
 const modules=['Interface','Concrete','Controls','TargetRepeat','ScopeTransport','WordBridge'].map(n=>'Solidity/Yul/Composition/'+n+'.lean');
 if(!equal(Object.keys(record.consumerModuleHashes??{}).sort(),modules.sort()))throw Error('missing component module');
 for(const f of modules)if(sha(readFileSync(join(ROOT,f)))!==record.consumerModuleHashes[f])throw Error('stale component proof body');
 if(!equal(record.producerHeads,['250555de2df2c16e2413cf329f43c77ce51ac8b6','9c631ecb07af62039348239763e049275fd78c1e','bea6e0e334f448aebb6f7c7a68321b4e419b43d2','2bb7bb20852e986f81a44aaaadfda104cac9c3f4']))throw Error('wrong component producer heads');
 for(const [key,source] of [['obligations',original.obligations],['combinations',original.combinations]]) {
  if(record[key]?.length!==source.length||!equal(record[key].map(x=>x.id),source.map(x=>x.id))||record[key].some(x=>x.fullStatus!=='pending'))throw Error('missing/closed original component obligation');
  for(let i=0;i<source.length;i++){if(!equal(record[key][i][key==='obligations'?'dependencies':'required'],source[i].dependencies)||key==='obligations'&&record[key][i].owner!==source[i].owner)throw Error('component dependency/owner drift');}
 }
 return record;
}
export function verifyInputs(dependency) {
 const p=verifyProducerReceipt(readFileSync(join(ROOT,'tests/yul-composition/producer-inputs.json')));
 const v16Bytes=readFileSync(join(ROOT,'tests/yul-composition/v16-producer-input.json'));if(sha(v16Bytes)!==V16_SHA)throw Error('V16 receipt drift');
 for(const m of JSON.parse(v16Bytes).modules)if(sha(readFileSync(join(dependency,m.module)))!==m.sha256)throw Error('V16 module drift');
 for(const pkg of p.packages)for(const m of pkg.modules)
  if(sha(readFileSync(join(dependency,m.module)))!==m.sha256)throw Error('producer body drift: '+m.module);
 const own=['Interface','Concrete','Controls','TargetRepeat','ScopeTransport','WordBridge'].map(n=>'Solidity/Yul/Composition/'+n+'.lean').concat('tests/yul-composition/ComponentDriver.lean');
 for(const f of own)if(!readFileSync(join(ROOT,f)).equals(readFileSync(join(dependency,f))))throw Error('consumer body drift: '+f);
 if(sha(readFileSync(join(ROOT,'tests/yul-composition/ComponentControls.sol')))!==SOURCE_SHA)throw Error('component source drift');
 return {v16InputSha256:V16_SHA,producerInputsSha256:sha(readFileSync(join(ROOT,'tests/yul-composition/producer-inputs.json'))),
  consumerHashes:Object.fromEntries(own.map(f=>[f,sha(readFileSync(join(ROOT,f)))]))};
}
export function compareProjection(lean,actual) {
 validateLean(lean);
 if(!actual||actual.address!==predictedAliases().self||!Array.isArray(actual.logs))throw Error('missing/malformed actual projection');
 const expectedLogs=[{emitter:actual.address,topics:[],data:'0x11'}];
 return equal(actual.pair,word(lean.word[0])) && actual.pairResult?.failed===false && actual.pairResult.exception===null && equal(actual.pairResult.logs,[]) && actual.pairResult.returnData===actual.pair && actual.failed===false && actual.bytes==='0xabcd' &&
  actual.storage===word(lean.revert[1]) && equal(actual.logs,expectedLogs) ? 'match':'mismatch';
}
export function validateComponentReport(r,rawDirectory) {
 if(typeof rawDirectory!=='string')throw Error('missing raw compiler evidence');
 validateLean(r.lean);validateComponentLedger(JSON.parse(readFileSync(join(ROOT,'tests/yul-composition/component-ledger.json'))));
 if(r.schema!==1||r.scope!==SCOPE||r.fullProofGate!=='pending'||r.sourceSha256!==SOURCE_SHA||r.producerInputsSha256!==PRODUCER_SHA||r.v16InputSha256!==V16_SHA||r.componentLedgerSha256!==sha(readFileSync(join(ROOT,'tests/yul-composition/component-ledger.json'))))throw Error('stale component report identity');
 const ledger=JSON.parse(readFileSync(join(ROOT,'tests/yul-composition/component-ledger.json')));if(!equal(r.readyComponentFacts,ledger.facts.map(f=>f.name)))throw Error('ready component fact drift');
 const profiles=[['legacy',false],['legacy',true],['viaIR',false],['viaIR',true]];
 if(!equal(r.rows?.map(x=>[x.pipeline,x.optimized]),profiles))throw Error('missing/reordered component profile');
 const own=['Interface','Concrete','Controls','TargetRepeat','ScopeTransport','WordBridge'].map(n=>'Solidity/Yul/Composition/'+n+'.lean').concat('tests/yul-composition/ComponentDriver.lean');
 if(!equal(Object.keys(r.consumerHashes??{}).sort(),[...own].sort())||own.some(f=>sha(readFileSync(join(ROOT,f)))!==r.consumerHashes[f]))throw Error('stale consumer proof receipt');
 const source=readFileSync(join(ROOT,'tests/yul-composition/ComponentControls.sol'),'utf8');
 for(const row of r.rows){
  const input=inputFor({'ComponentControls.sol':{content:source}},row.pipeline,row.optimized);
  const stem=join(rawDirectory,row.pipeline+(row.optimized?'-optimized':''));const raw=readFileSync(stem+'.output.json','utf8');
  const savedInput=JSON.parse(readFileSync(stem+'.input.json'));if(!equal(savedInput,input))throw Error('stale raw compiler input');
  validateProvenance(row.receipt,input,raw);
  const artifact=JSON.parse(raw).contracts['ComponentControls.sol'].ComponentControls;
  if(row.receipt.inputSha256!==sha(JSON.stringify(input))||!equal(row.receipt.settings,input.settings)||row.receipt.pipeline!==row.pipeline)throw Error('stale component call/profile receipt');
  bindCapture(row.deployment,row.deploymentResult,{transaction:1,to:null,input:'0x'+artifact.evm.bytecode.object});
  if(row.deploymentResult.failed||row.deploymentResult.logs.length||row.deploymentResult.returnData!=='0x'+artifact.evm.deployedBytecode.object||row.pairCapture.pre[row.actual.address]?.code!=='0x'+artifact.evm.deployedBytecode.object)throw Error('constructor result mismatch');
  bindCapture(row.pairCapture,row.actual.pairResult,{transaction:2,to:row.actual.address,input:row.pairCapture.request.input});
  bindCapture(row.caughtCapture,row.caughtResult,{transaction:3,to:row.actual.address,input:row.caughtCapture.request.input});
  for(const [signature,capture] of [['pair()',row.pairCapture],['caught()',row.caughtCapture]]){const expected='0x'+Buffer.from(keccak_256(new TextEncoder().encode(signature))).subarray(0,4).toString('hex');if(capture.request.input!==expected||capture.frames[0].input!==expected)throw Error('component request identity drift');}
  const wrote42=row.caughtCapture.operations.some(o=>o.kind==='putStorage'&&o.address===row.actual.address&&o.value===word(42));
  if(row.caughtCapture.frames.length!==2||!row.optimized&&!wrote42||row.internalWrite42!==wrote42||row.internalTraceAgreement!=='pending; optimizer may remove reverted writes, not observable state')throw Error('nested component trace evidence drift');
  if(row.actual.failed!==row.caughtResult.failed||row.actual.bytes!==row.caughtResult.returnData||!equal(row.actual.logs,row.caughtResult.logs)||row.actual.storage!==row.caughtCapture.post[row.actual.address]?.persistent?.[word(0)]||row.status!=='match'||compareProjection(r.lean,row.actual)!=='match')throw Error('component projection/capture mismatch');
 }
 const runtime=Buffer.from([...r.lean.code,0x60,0,0x52,0x60,32,0x60,0,0xf3]);
 const init=Buffer.concat([Buffer.from([0x60,runtime.length,0x60,12,0x60,0,0x39,0x60,runtime.length,0x60,0,0xf3]),runtime]);
 const t=r.target;
 bindCapture(t.deploymentCapture,t.deploymentResult,{transaction:1,to:null,input:bytesToHex(init)});
 bindCapture(t.capture,t.observation,{transaction:2,to:predictedAliases().self,input:'0x'});
 if(t.deploymentResult.failed!==false||t.deploymentResult.exception!==null||t.deploymentResult.logs.length||t.deploymentResult.returnData!==bytesToHex(runtime)||t.capture.pre[predictedAliases().self]?.code!==t.deploymentResult.returnData||t.code!==runtime.toString('hex')||t.runtimeSha256!==sha(runtime)||t.initcodeSha256!==sha(init)||t.capture.pre[predictedAliases().self]?.code!==bytesToHex(runtime)||t.failed!==false||t.observation.failed!==false||t.observation.logs.length||t.actual!==word(r.lean.word[0])||t.actual!==t.observation.returnData||t.status!=='match')throw Error('encoded target evidence mismatch');
 return r;
}
export async function runComponents({compiler,dependency,out}) {
 mkdirSync(out,{recursive:true});const bindings=verifyInputs(dependency);
 const componentLedger=validateComponentLedger(JSON.parse(readFileSync(join(ROOT,'tests/yul-composition/component-ledger.json'))));
 const run=spawnSync('/workspace/.setup/tools/lean-4.24.0-linux/bin/lake',['-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/ComponentDriver.lean'],{cwd:dependency,encoding:'utf8',env:{...process.env,LEAN_NUM_THREADS:'1'}});
 writeFileSync(join(out,'lean.stdout'),run.stdout??'');writeFileSync(join(out,'lean.stderr'),run.stderr??'');
 if(run.status!==0)throw Error('actual component execution failed: '+run.status);
 const lean=validateLean(JSON.parse(run.stdout));writeFileSync(join(out,'lean.json'),JSON.stringify(lean,null,2)+'\n');
 const compile=checkedCompiler(compiler),source=readFileSync(join(ROOT,'tests/yul-composition/ComponentControls.sol'),'utf8'),rows=[];
 for(const pipeline of ['legacy','viaIR'])for(const optimized of [false,true]) {
  const input=inputFor({'ComponentControls.sol':{content:source}},pipeline,optimized),stem=join(out,pipeline+(optimized?'-optimized':''));
  const receipt=compileRecord(compile,input,stem);if(receipt.errors.length)throw Error('component compiler error: '+JSON.stringify(receipt.errors));
  const artifact=receipt.output.contracts['ComponentControls.sol'].ComponentControls;
  const {vm,observer}=await capturedMachine();let ordinal=0;const call=opts=>observer.run(opts,++ordinal);
  const deploy=await call({data:hexToBytes('0x'+artifact.evm.bytecode.object)}),addr=deploy.result.createdAddress;
  const deploymentResult=observed(deploy);bindCapture(deploy.capture,deploymentResult,{transaction:1,to:null,input:'0x'+artifact.evm.bytecode.object});
  if(deploymentResult.failed||deploymentResult.logs.length||!addr)throw Error('component deploy failed/log mismatch');
  if(bytesToHex(await vm.evm.stateManager.getCode(addr))!=='0x'+artifact.evm.deployedBytecode.object)throw Error('component runtime installation mismatch');
  const invoke=sig=>call({to:addr,data:hexToBytes('0x'+artifact.evm.methodIdentifiers[sig])});
  const pair=await invoke('pair()'),caught=await invoke('caught()');validateCapture(caught.capture);
  const pairResult=observed(pair),caughtResult=observed(caught);
  bindCapture(pair.capture,pairResult,{transaction:2,to:addr.toString(),input:'0x'+artifact.evm.methodIdentifiers['pair()']});
  bindCapture(caught.capture,caughtResult,{transaction:3,to:addr.toString(),input:'0x'+artifact.evm.methodIdentifiers['caught()']});
  const e=caught.result.execResult,exception=checkException(e.exceptionError?.error??null),address=addr.toString();
  const actual={address,pairResult,pair:bytesToHex(pair.result.execResult.returnValue),failed:!!exception,bytes:bytesToHex(e.returnValue),storage:caught.capture.post[address]?.persistent?.[word(0)],logs:(e.logs??[]).map(([a,t,d])=>({emitter:bytesToHex(a),topics:t.map(bytesToHex),data:bytesToHex(d)}))};
  writeFileSync(stem+'.capture.json',JSON.stringify({actual,capture:caught.capture},null,2)+'\n');
  const proofOfWrite=caught.capture.operations.some(o=>o.kind==='putStorage'&&o.address===address&&o.value===word(42));
  // Missing evidence is an error, not empty state or a downgraded comparison.
  if((!optimized&&!proofOfWrite)||caught.capture.frames.length!==2||!actual.storage)throw Error('missing nested write/frame/state capture: '+JSON.stringify({proofOfWrite,frames:caught.capture.frames.length,actual}));
  rows.push({pipeline,optimized,internalWrite42:proofOfWrite,internalTraceAgreement:'pending; optimizer may remove reverted writes, not observable state',receipt:receipt.record,actual,caughtResult,status:compareProjection(lean,actual),deploymentResult,deployment:deploy.capture,pairCapture:pair.capture,caughtCapture:caught.capture});
 }
 // Execute the exact emitted backend ADD bytes, independently of solc.
 const runtime=Buffer.from([...lean.code,0x60,0,0x52,0x60,32,0x60,0,0xf3]);
 const init=Buffer.concat([Buffer.from([0x60,runtime.length,0x60,12,0x60,0,0x39,0x60,runtime.length,0x60,0,0xf3]),runtime]);
 const {vm,observer}=await capturedMachine();const d=await observer.run({data:init},1),a=d.result.createdAddress;
 const deploymentResult=observed(d);bindCapture(d.capture,deploymentResult,{transaction:1,to:null,input:bytesToHex(init)});
 if(!a||deploymentResult.failed||deploymentResult.logs.length)throw Error('encoded component deploy failed');
 if(bytesToHex(await vm.evm.stateManager.getCode(a))!==bytesToHex(runtime))throw Error('encoded runtime installation mismatch');
 const t=await observer.run({to:a},2),actual=observed(t);bindCapture(t.capture,actual,{transaction:2,to:a.toString(),input:'0x'});
 const target={code:runtime.toString('hex'),initcodeSha256:sha(init),runtimeSha256:sha(runtime),actual:actual.returnData,failed:actual.failed,observation:actual,deploymentResult,deploymentCapture:d.capture,capture:t.capture};
 target.status=!target.failed&&target.observation.logs.length===0&&target.actual===word(lean.word[0])?'match':'mismatch';
 const result={schema:1,scope:SCOPE,...bindings,componentLedgerSha256:sha(readFileSync(join(ROOT,'tests/yul-composition/component-ledger.json'))),readyComponentFacts:componentLedger.facts.map(f=>f.name),sourceSha256:sha(source),lean,rows,target,fullProofGate:'pending'};
 validateComponentReport(result,out);
 writeFileSync(join(out,'report.json'),JSON.stringify(result,null,2)+'\n');
 if(rows.some(r=>r.status!=='match')||target.status!=='match')throw Error('actual component differential mismatch');return result;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
 const [, ,compiler,dependency,out]=process.argv;if(!out)throw Error('usage: component.mjs COMPILER DEPENDENCY OUT');
 const r=await runComponents({compiler,dependency,out});console.log(JSON.stringify({profiles:r.rows.length,encodedTarget:r.target.status,fullProofGate:r.fullProofGate}));
}
