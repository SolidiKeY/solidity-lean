/** Lane-owned byte-vector reference. Shared parser and bounded engine are read-only. */
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {isDeepStrictEqual} from 'node:util';
import {parseFixture,withPreamble,runtimePipelines,revertBytes,abiType,evmCompatible} from '../solidity-upstream.mjs';
import {machine,INITIAL_GAS,STEP_LIMIT} from '../evm-reference/replay.mjs';
import {Account,createAddressFromString,hexToBytes,bytesToHex} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
const ROOT=fileURLToPath(new URL('../../',import.meta.url));
const sha=b=>createHash('sha256').update(b).digest('hex');
const hex=b=>'0x'+Buffer.from(b).toString('hex');
export const HOST={sender:'0x1212121212121212121212121212120000000012',origin:'0x9292929292929292929292929292929292929292',funding:(1n<<100n).toString(),chainId:'1',coinbase:'0x7878787878787878787878787878787878787878',prevrandao:'0xa86c2e601b6c44eb4848f7d23d9df3113fbcac42041c49cbed5000cb4f118777',gasLimit:'20000000',gasPrice:'3000000000',baseFee:'7',blobBaseFee:'1',blobHashes:['0x0100000000000000000000000000000000000000000000000000000000000001','0x0100000000000000000000000000000000000000000000000000000000000002'],source:'test/EVMHost.cpp:146-168,206-231;test/EVMHost.h:86-91;test/ExecutionFramework.cpp:81-86,148-183,245-248'};
const bytes=text=>text.trim()?revertBytes(text):[];
function stripComments(text) {
 let quoted=false,escape=false,out='';
 for(let i=0;i<text.length;i++) {const c=text[i];
  if(!quoted&&c==='#'){const end=text.indexOf('#',i+1);if(end<0)throw Error('unterminated fixture comment');i=end;out+=' ';continue;}
  out+=c;if(escape)escape=false;else if(quoted&&c==='\\')escape=true;else if(c==='"')quoted=!quoted;
 }if(quoted)throw Error('unterminated string');return out.trim();
}
function splitParameters(text) {
 let q=false,e=false,start=0;const parts=[];
 for(let i=0;i<text.length;i++){const c=text[i];if(e)e=false;else if(q&&c==='\\')e=true;else if(c==='"')q=!q;else if(c===','&&!q){parts.push(text.slice(start,i).trim());start=i+1;}}
 if(q)throw Error('unterminated log string');if(text.trim())parts.push(text.slice(start).trim());return parts;
}
export function parseLog(line) {
 const m=/^~\s*emit\s+<anonymous>(?:\s+from\s+(0x[\da-fA-F]{40}))?\s*(?::\s*(.*))?$/.exec(line.trim());
 if(!m)throw Error('unadapted event expectation: '+line);
 const topics=[],data=[];let dataStarted=false;
 for(const token of splitParameters(m[2]??'')) {
  if(token.startsWith('#')){if(dataStarted)throw Error('log topic after data');const b=bytes(token.slice(1));if(b.length!==32)throw Error('log topic must be one word');topics.push(hex(b));}
  else{dataStarted=true;data.push(...bytes(token));}
 }return {emitter:m[1]?.toLowerCase()??'self',topics,data:hex(data)};
}
/** TestFileParser permits omitted arrows for successful empty output. Every
 * original line is assigned to a call/log/metadata record or rejected. */
export function parseExpectations(lines) {
 const calls=[],records=[];
 for(const [index,raw]of lines.entries()) {
  const trimmed=raw.trim();if(!trimmed){records.push({line:index,raw,kind:'blank'});continue;}
  if(trimmed.startsWith('gas ')) {
   const m=/^gas (legacy|legacyOptimized|ir|irOptimized|ssaCFG|ssaCFGOptimized)( code)?: (\d+)$/.exec(trimmed);
   if(!m||!calls.length)throw Error('unadapted gas metadata at '+index+': '+raw);
   const gas={line:index,raw,kind:'gas-metadata',profile:m[1],codeDeposit:!!m[2],value:m[3],semanticObservation:false};calls.at(-1).gas.push(gas);records.push(gas);continue;
  }
  if(trimmed.startsWith('~')){if(!calls.length)throw Error('orphan side effect');const log=parseLog(trimmed);calls.at(-1).logs.push(log);records.push({line:index,raw,kind:'log',call:calls.length-1,expected:log});continue;}
  const line=stripComments(trimmed),m=/^([\w$]+)\(/.exec(line);if(!m)throw Error('unadapted call at '+index+': '+raw);
  let depth=0,end=-1;for(let i=m[1].length;i<line.length;i++){if(line[i]==='(')depth++;if(line[i]===')'&&--depth===0){end=i+1;break;}}
  if(end<0)throw Error('unclosed call signature');
  const signature=line.slice(0,end),tail=line.slice(end),rest=/^\s*(?:,\s*(\d+)\s+(wei|ether))?\s*(?::\s*(.*?))?\s*(?:->\s*(.*))?$/.exec(tail);
  if(!rest)throw Error('unadapted call tail: '+tail);
  if(rest[3]!==undefined&&!rest[3].trim())throw Error('empty argument list after colon');
  const expected=(rest[4]??'').trim(),failure=expected==='FAILURE'||expected.startsWith('FAILURE,');
  if(expected.startsWith('FAILURE')&&!failure)throw Error('malformed failure expectation');
  const payload=failure?(expected==='FAILURE'?'':expected.slice(8).trim()):expected;
  const call={line:index,raw,signature,constructor:m[1]==='constructor',calldata:bytes(rest[3]??''),value:(BigInt(rest[1]??0)*(rest[2]==='ether'?10n**18n:1n)).toString(),failure,expectedBytes:bytes(payload),logs:[],gas:[]};
  if(call.constructor&&calls.length)throw Error('redeployment after calls not adapted');
  calls.push(call);records.push({line:index,raw,kind:'call',call:calls.length-1});
 }if(!calls.length)throw Error('no calls');return {calls,records};
}
export function profilesFor(fixture,plan) {
 const required=runtimePipelines(fixture.settings),profiles=required.map(pipeline=>({name:pipeline==='viaIR'?'ir':'legacy',pipeline,optimized:false,required:true}));
 const ssa=fixture.settings.compileViaSSACFG??'true';if(!['true','false'].includes(ssa))throw Error('invalid compileViaSSACFG');
 // SemanticTest.cpp:110,332-337 enables SSA-CFG by default when viaIR runs.
 if(ssa==='true'&&required.includes('viaIR'))profiles.push({name:'ssaCFGOptimized',pipeline:'viaIR',optimized:true,ssaCFG:true,required:true});
 for(const name of new Set(plan.calls.flatMap(c=>c.gas.map(g=>g.profile)))) {
  if(profiles.some(p=>p.name===name))continue;const pipeline=['legacy','legacyOptimized'].includes(name)?'legacy':'viaIR';
  if(name==='ssaCFG'||name==='ssaCFGOptimized')profiles.push({name,pipeline:'viaIR',optimized:name==='ssaCFGOptimized',ssaCFG:true,required:false});
  else if(required.includes(pipeline))profiles.push({name,pipeline,optimized:true,required:false});
  else profiles.push({name,required:false,blocked:'Gas metadata profile is not requested by compileViaYul; metadata retained'});
 }return profiles;
}
export function exactObservation(exec,metrics) {
 const exception=exec.exceptionError?.error??null;
 if(exception&&!['revert','out of gas','stack overflow'].includes(exception))throw Error('unadapted engine exception: '+exception);
 if(!(exec.returnValue instanceof Uint8Array)||!Array.isArray(exec.logs))throw Error('missing/malformed EVM return bytes or logs');
 return {failed:!!exception,exception,returnData:hex(exec.returnValue),logs:exec.logs.map(log=>{
  if(!Array.isArray(log)||log.length!==3||!(log[0]instanceof Uint8Array)||log[0].length!==20||!Array.isArray(log[1])||!log[1].every(t=>t instanceof Uint8Array&&t.length===32)||!(log[2]instanceof Uint8Array))throw Error('malformed EVM log');
  return {emitter:hex(log[0]),topics:log[1].map(hex),data:hex(log[2])};
 }),metrics,gasUsedTelemetry:exec.executionGasUsed.toString()};
}
export function compareCall(call,actual,address,{creation=false}={}) {
 if(!actual||typeof actual.failed!=='boolean'||typeof actual.returnData!=='string'||!/^0x(?:[0-9a-f]{2})*$/i.test(actual.returnData)||!Array.isArray(actual.logs))throw Error('missing/malformed actual observation');
 if(![null,'revert','out of gas','stack overflow'].includes(actual.exception)||actual.failed!==(actual.exception!==null))throw Error('inconsistent actual failure evidence');
 for(const log of actual.logs)if(!log||!/^0x[0-9a-f]{40}$/i.test(log.emitter)||!Array.isArray(log.topics)||!log.topics.every(t=>/^0x[0-9a-f]{64}$/i.test(t))||!/^0x(?:[0-9a-f]{2})*$/i.test(log.data))throw Error('malformed actual log evidence');
 const expected={failed:call.failure,returnData:hex(call.expectedBytes),logs:call.logs.map(l=>({...l,emitter:l.emitter==='self'?address:l.emitter}))};const differences=[];
 if(expected.failed!==actual.failed)differences.push('failure');
 // CREATE success returns code: preserve/check it as installation evidence.
 if(!(creation&&!actual.failed)&&expected.returnData!==actual.returnData)differences.push('bytes');
 if(creation&&!actual.failed&&call.expectedBytes.length)throw Error('constructor ABI output expectation not adapted');
 if(!isDeepStrictEqual(expected.logs,actual.logs))differences.push('logs');
 return {status:differences.length?'broken':'working',differences,expected};
}
function walk(n,fn){if(!n||typeof n!=='object')return;fn(n);for(const v of Object.values(n))if(Array.isArray(v)){for(const a of v)walk(a,fn);}else if(v&&typeof v==='object')walk(v,fn);}
export function osakaCompatible(constraint) {
 // Pinned EVMHost.cpp:136-142 selects Osaka before Amsterdam. We execute
 // Osaka only; the future-fork bound does not request Amsterdam execution.
 if(constraint==='<amsterdam')return true;
 return evmCompatible(constraint);
}
function hostSupport(ast) {
 const reasons=[];walk(ast,n=>{if(n.nodeType==='FunctionCall'&&n.expression?.name==='blockhash'||n.nodeType==='YulFunctionCall'&&n.functionName?.name==='blockhash')reasons.push('blockhash history host not adapted');});return [...new Set(reasons)];
}
export async function beginFrame(evm,previous) {
 const deletedAccounts=[];
 if(previous && !previous.exceptionError) for(const address of previous.selfdestruct?.keys()??[]) {
  if(previous.createdAddresses?.has(address)) {const account=createAddressFromString(address);
   // The exported SimpleStateManager deletes only account metadata; code and
   // storage are separate maps. Clear both using public primitives first.
   await evm.stateManager.putCode(account,new Uint8Array());await evm.stateManager.clearStorage(account);await evm.stateManager.deleteAccount(account);
   if((await evm.stateManager.getCode(account)).length||(await evm.stateManager.getAccount(account))!==undefined)throw Error('incomplete selfdestruct finalization');
   deletedAccounts.push(address);}
 }
 const transientBeforeReset=evm.transientStorage.toJSON();evm.transientStorage.clear();
 return {deletedAccounts,transientBeforeReset,transientReset:true};
}
export async function replay(artifact,plan) {
 if(!plan||!Array.isArray(plan.calls)||!plan.calls.length)throw Error('missing call plan');
 const vm=await machine();const sender=createAddressFromString(HOST.sender),origin=createAddressFromString(HOST.origin);
 await vm.evm.stateManager.deleteAccount(createAddressFromString('0x'+'12'.repeat(20)));
 for(let i=0;i<10;i++)await vm.evm.stateManager.putAccount(createAddressFromString('0x'+(BigInt(HOST.sender)+BigInt(i)*0x1000n).toString(16).padStart(40,'0')),new Account(0n,1n<<100n));
 for(let i=1;i<=8;i++)await vm.evm.stateManager.putAccount(createAddressFromString('0x'+i.toString(16).padStart(40,'0')),new Account(0n,1n));
 let transaction=0,address;const observed=[];let deployment,previous=null;
 async function call(data,value,to) {
  transaction++;const frame=await beginFrame(vm.evm,previous);
  const block={header:{number:BigInt(transaction),timestamp:15n*BigInt(transaction),coinbase:createAddressFromString(HOST.coinbase),difficulty:200000000n,prevRandao:hexToBytes(HOST.prevrandao),gasLimit:20000000n,baseFeePerGas:7n,getBlobGasPrice:()=>1n}};
  const response=await vm.call({caller:sender,origin,data:hexToBytes(data),value:BigInt(value),...(to?{to}:{}),block,gasPrice:3000000000n,blobVersionedHashes:HOST.blobHashes});
  previous=response.result.execResult;
  return {...response,transaction,frame,requestData:data};
 }
 async function deploy(c) {
  const r=await call('0x'+artifact.evm.bytecode.object+Buffer.from(c.calldata).toString('hex'),c.value);
  const actual=exactObservation(r.result.execResult,r.metrics),addr=r.result.createdAddress?.toString()??null,record={transaction:r.transaction,frame:r.frame,requestData:r.requestData,actual,address:addr};
  if(!actual.failed){if(!addr)throw Error('successful creation without address');address=r.result.createdAddress;const installed=bytesToHex(await vm.evm.stateManager.getCode(address));if(installed!==actual.returnData)throw Error('creation output differs from installed runtime');record.installedRuntime=installed;record.runtimeSha256=sha(hexToBytes(installed));}
  return record;
 }
 if(!plan.calls[0].constructor){deployment=await deploy({calldata:[],value:'0'});if(deployment.actual.failed||deployment.actual.logs.length)return {status:'blocked',reason:'implicit deployment failed or emitted unlisted logs',deployment,observed,expectedCallCount:plan.calls.length};}
 let mismatch=false;
 for(const [index,c]of plan.calls.entries()) {
  try {
   let actual,record;
   if(c.constructor){record=await deploy(c);deployment=record;actual=record.actual;}
   else {
    if(!address)throw Error('call after failed creation not adapted');
    if(!Array.isArray(artifact.abi)||artifact.abi.some(d=>d.type==='function'&&!Array.isArray(d.inputs)))throw Error('malformed ABI function inputs');
    const declaration=artifact.abi.find(d=>d.type==='function'&&`${d.name}(${d.inputs.map(abiType).join(',')})`===c.signature),selector=artifact.evm.methodIdentifiers[c.signature];
    if(!declaration||!selector)throw Error('missing ABI declaration/selector: '+c.signature);
    if(!Array.isArray(c.calldata)||!Array.isArray(c.expectedBytes))throw Error('missing byte-vector evidence');
    const result=await call('0x'+selector+Buffer.from(c.calldata).toString('hex'),c.value,address);actual=exactObservation(result.result.execResult,result.metrics);record={transaction:result.transaction,frame:result.frame,requestData:result.requestData};
   }
   const comparison=compareCall(c,actual,address?.toString()??null,{creation:c.constructor});observed.push({index,signature:c.signature,inputBytes:hex(c.calldata),value:c.value,...record,actual,comparison});mismatch ||=comparison.status==='broken';
  }catch(e){return {status:mismatch?'broken':'blocked',reason:e.message,stack:e.stack,deployment,observed,blockedCall:index,expectedCallCount:plan.calls.length};}
 }
 return {status:mismatch?'broken':'working',deployment,observed,expectedCallCount:plan.calls.length};
}
function fixtureInput(fixture,profile) {
 const sources=Object.fromEntries([...fixture.sources].map(([name,source])=>[name,{content:withPreamble(source)}]));
    const experimental=fixture.settings.experimental??fixture.settings.compileViaSSACFG??'true';if(!['true','false'].includes(experimental))throw Error('invalid experimental setting');
    const settings={experimental:experimental==='true',...(profile.ssaCFG?{viaSSACFG:true}:{}),viaIR:profile.pipeline==='viaIR',evmVersion:'osaka',optimizer:{enabled:profile.optimized,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers']}}};
    return {language:'Solidity',sources,settings};
}
export async function runFixture(path,directory,compile,scanPolicy) {
 const raw=readFileSync(join(directory,path)),manifest=JSON.parse(readFileSync(join(ROOT,'tests/upstream/snapshot.json'))),pin=manifest.files.find(f=>f.path===path);
 if(!pin||raw.length!==pin.bytes||sha(raw)!==pin.sha256)throw Error('unpinned fixture bytes: '+path);
 const fixture=parseFixture(new TextDecoder('utf8',{fatal:true}).decode(raw));
 const result={path,sourceSha256:sha(raw),originalSettings:fixture.settings,originalExpectations:fixture.expectations,stage:'vy5-reference-bytes',scope:'External byte/log reference only; no admission/correspondence proof or complete world/final-memory comparison. EthereumJS CREATE address convention differs from pinned EVMHost pre-increment; concrete CREATE-address-dependent oracles are not adapted.',requiredPipelines:runtimePipelines(fixture.settings),environment:HOST,initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,variants:[]};
 try {
  const plan=parseExpectations(fixture.expectations);result.plan=plan;
  for(const profile of profilesFor(fixture,plan)) {
   const v={...profile,status:'blocked'};result.variants.push(v);
   try {
    if(profile.blocked)throw Error(profile.blocked);
    const unknown=Object.keys(fixture.settings).filter(k=>!['EVMVersion','compileViaYul','compileViaSSACFG','experimental'].includes(k));if(unknown.length)throw Error('unadapted settings: '+unknown.join(','));
    if(!osakaCompatible(fixture.settings.EVMVersion))throw Error('fixture EVM constraint excludes Osaka: '+fixture.settings.EVMVersion);
    const input=fixtureInput(fixture,profile),settings=input.settings;v.settings=settings;v.inputSha256=sha(JSON.stringify(input));
    const output=compile(input);v.errors=(output.errors??[]).filter(e=>e.severity==='error');if(v.errors.length)throw Error('reference compiler rejection');
    const ast=output.sources[fixture.mainSource].ast,unsupported=hostSupport(ast);if(unsupported.length)throw Error(unsupported.join(';'));
    const contract=ast.nodes.filter(n=>n.nodeType==='ContractDefinition'&&n.contractKind==='contract'&&!n.abstract).at(-1)?.name;if(!contract)throw Error('no concrete deployment contract');v.contract=contract;v.policy=(scanPolicy??(await import('./harness.mjs')).policyScan)(ast);
    const artifact=output.contracts[fixture.mainSource][contract];
    let creates=false;walk(ast,n=>{if(n.nodeType==='NewExpression'||n.nodeType==='YulFunctionCall'&&['create','create2'].includes(n.functionName?.name))creates=true;});
    if(creates&&plan.calls.some(c=>artifact.abi.some(d=>d.type==='function'&&`${d.name}(${d.inputs.map(abiType).join(',')})`===c.signature&&d.outputs.some(o=>o.type==='address'))))throw Error('concrete creation-address oracle not adapted to upstream nonce convention');
    v.creationSha256=sha(Buffer.from(artifact.evm.bytecode.object,'hex'));v.runtimeTemplateSha256=sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex'));Object.assign(v,await replay(artifact,plan));
   }catch(e){v.reason=e.message;v.stack=e.stack;}
  }
 }catch(e){result.reason=e.message;result.stack=e.stack;}
 result.status=result.variants.some(v=>v.status==='broken')?'broken':result.variants.length&&result.variants.every(v=>v.status==='working')?'working':'blocked';return result;
}

/** Data completeness check, not a correctness theorem. Broken observations
 * dominate later adapter blocks; a working row must contain the complete plan. */
export function validateFixtureEvidence(result,directory) {
 if(!directory)throw Error('missing pinned corpus directory');
 const snapshot=JSON.parse(readFileSync(join(ROOT,'tests/upstream/snapshot.json'))),pin=snapshot.files.find(f=>f.path===result?.path);
 if(!pin)throw Error('unregistered fixture evidence');
 const raw=readFileSync(join(directory,pin.path));if(raw.length!==pin.bytes||sha(raw)!==pin.sha256||result.sourceSha256!==pin.sha256)throw Error('stale fixture bytes/hash');
 const original=parseFixture(new TextDecoder('utf8',{fatal:true}).decode(raw));
 if(!isDeepStrictEqual(original.settings,result.originalSettings)||!isDeepStrictEqual(original.expectations,result.originalExpectations))throw Error('changed pinned settings/expectations');
 if(!result||!Array.isArray(result.originalExpectations)||!result.originalSettings||!Array.isArray(result.variants))throw Error('missing fixture evidence');
 const fixture={settings:result.originalSettings},plan=parseExpectations(result.originalExpectations);
 if(!isDeepStrictEqual(plan,result.plan)||!isDeepStrictEqual(runtimePipelines(fixture.settings),result.requiredPipelines))throw Error('changed/missing original plan or pipelines');
 const profiles=profilesFor(fixture,plan);
 if(result.variants.length!==profiles.length)throw Error('missing/extra runtime profile');
 let broken=false,blocked=false;
 for(const profile of profiles) {
  const matches=result.variants.filter(v=>v.name===profile.name);
  if(matches.length!==1)throw Error('missing/duplicate runtime profile');
  const v=matches[0];
  for(const k of ['pipeline','optimized','required','ssaCFG'])if(v[k]!==profile[k])throw Error('changed runtime profile');
  if(!['working','broken','blocked'].includes(v.status))throw Error('unknown runtime verdict');
  if(profile.blocked&&v.status!=='blocked')throw Error('unsupported profile claimed executed');
  if(v.settings||v.status==='working') {
   const input=fixtureInput(original,profile);
   if(!isDeepStrictEqual(input.settings,v.settings)||sha(JSON.stringify(input))!==v.inputSha256)throw Error('changed compiler settings/input hash');
  }
  const observations=v.observed;
  if(v.status==='working') {
   const d=v.deployment,a=d?.actual;
   if(!a?.metrics||!Number.isSafeInteger(a.metrics.steps)||a.metrics.steps<0||a.metrics.steps>STEP_LIMIT)throw Error('invalid deployment metrics');
   if(plan.calls[0].constructor) {
    const o=observations?.[0];
    for(const k of ['actual','transaction','frame','requestData'])if(!isDeepStrictEqual(d[k],o?.[k]))throw Error('inconsistent explicit deployment evidence');
   } else {
    const c={failure:false,expectedBytes:[],logs:[]};
    if(compareCall(c,a,d.address,{creation:true}).status!=='working'||d.transaction!==1)throw Error('invalid implicit deployment observation');
   }
  }
  if(v.status==='working'&&(!v.deployment||!v.deployment.actual))throw Error('missing deployment evidence');
  if(v.status==='working'&&!v.deployment.actual.failed&&(!/^0x[0-9a-f]{40}$/i.test(v.deployment.address)||v.deployment.installedRuntime!==v.deployment.actual.returnData||v.deployment.runtimeSha256!==sha(Buffer.from(v.deployment.installedRuntime.slice(2),'hex'))))throw Error('malformed installation evidence');
  if(v.status==='working'&&(!Array.isArray(observations)||observations.length!==plan.calls.length||v.expectedCallCount!==plan.calls.length))throw Error('missing ordered observations');
  if(v.status==='blocked'&&typeof v.reason!=='string')throw Error('missing block reason');
  for(const [i,o]of (observations??[]).entries()) {
   if(!o.actual?.metrics||!Number.isSafeInteger(o.actual.metrics.steps)||o.actual.metrics.steps<0||o.actual.metrics.steps>STEP_LIMIT)throw Error('missing/invalid execution metrics');
   const c=plan.calls[i];if(!c||o.index!==i||o.signature!==c.signature||o.inputBytes!==hex(c.calldata)||o.value!==c.value)throw Error('changed/dropped/reordered call evidence');
   if(o.transaction!==i+(plan.calls[0].constructor?1:2))throw Error('transaction sequence mismatch');
   const comparison=compareCall(c,o.actual,v.deployment?.address??null,{creation:c.constructor});
   if(!isDeepStrictEqual(comparison,o.comparison))throw Error('malformed or stale comparison');
   if(comparison.status==='broken')broken=true;
  }
  if((observations??[]).some(o=>o.comparison.status==='broken')&&v.status!=='broken')throw Error('observed mismatch hidden by aggregate verdict');
  if(v.status==='broken')broken=true;if(v.status==='blocked')blocked=true;
 }
 const expected=broken?'broken':blocked?'blocked':'working';if(result.status!==expected)throw Error('incorrect fixture aggregate verdict');
 return {calls:plan.calls.length,profiles:profiles.length,status:result.status};
}
