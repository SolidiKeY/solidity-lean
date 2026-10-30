#!/usr/bin/env node
/** Payment-specific pinned-bytecode observations. Never merged into Lean coverage. */
import {readFileSync,writeFileSync,mkdirSync,mkdtempSync,rmSync} from 'node:fs';
import {resolve,dirname,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {hexToBytes,bytesToHex} from '@ethereumjs/util';
import {machine,observation,creationObservation,HostLimit,INITIAL_GAS,STEP_LIMIT} from './replay.mjs';
import {COMPILER_SHA,PIN,verifySnapshot,parseFixture,withPreamble,runtimePipelines,semanticVectors,revertBytes,evmCompatible} from '../solidity-upstream.mjs';
const ROOT=resolve(dirname(fileURLToPath(import.meta.url)),'../..');
const sha=x=>createHash('sha256').update(x).digest('hex');
const word=x=>BigInt.asUintN(256,BigInt(x)).toString(16).padStart(64,'0');
const hex=xs=>'0x'+xs.map(x=>x.toString(16).padStart(2,'0')).join('');
// Pinned EVMHost.cpp:306-318,420-437 and ExecutionFramework.cpp:191-196.
// No extra top-level initcode-word surcharge is added to this host formula.
export const HOST_GAS=Object.freeze({call:21000n,create:53000n,zero:4n,nonzero:16n,code:200n,refundDivisor:5n});
export function hostGas(data,creation,execution,refund,deposit) {
  if([execution,refund,deposit].some(x=>typeof x!=='bigint'||x<0n)) throw new HostLimit('invalid gas accounting input');
  const intrinsic=(creation?HOST_GAS.create:HOST_GAS.call)+data.reduce((n,b)=>n+(b?HOST_GAS.nonzero:HOST_GAS.zero),0n);
  const gross=intrinsic+execution;
  const applied=refund<gross/HOST_GAS.refundDivisor?refund:gross/HOST_GAS.refundDivisor;
  if(deposit>gross-applied) throw new HostLimit('unsupported negative non-code gas');
  return {intrinsic:intrinsic.toString(),gross:gross.toString(),refundApplied:applied.toString(),
    used:(gross-applied).toString(),codeDeposit:deposit.toString(),nonCode:(gross-applied-deposit).toString()};
}
const canonical=p=>p==='ir'?'viaIR':p;
export function paymentVectors(fixture,abi) {
  const vectors=[],gas=[],ordered=[];
  for(const [lineIndex,original] of fixture.expectations.entries()) {
    const line=original.trim(); if(!line) continue;
    const g=/^gas\s+(ir|irOptimized|legacy|legacyOptimized)(\s+code)?\s*:\s*(\d+)$/.exec(line);
    if(g) {
      if(!vectors.length) throw new HostLimit('gas observation without preceding call');
      const item={lineIndex,original,vector:vectors.length-1,profile:canonical(g[1]),label:g[1],code:!!g[2],expected:g[3]};
      gas.push(item);ordered.push({kind:'gas',...item});continue;
    }
    const call=/^(constructor\([^)]*\)|\(\)|[A-Za-z_$][\w$]*\([^)]*\))(?:\s*,\s*(\d+)\s*(wei|ether))?\s*(.*)$/.exec(line);
    if(!call) throw new HostLimit('unadapted payment observation: '+line);
    const value=BigInt(call[2]??0)*(call[3]==='ether'?10n**18n:1n);
    if(value>=2n**256n) throw new HostLimit('value outside ABI word');
    let vector;
    if(call[1]==='()') {
      const tail=/^->\s*(.*)$/.exec(call[4]);
      if(!tail) throw new HostLimit('unsupported empty-calldata observation');
      const failure=tail[1]==='FAILURE'||tail[1].startsWith('FAILURE,');
      const payload=failure?(tail[1]==='FAILURE'?'':tail[1].slice(8).trim()):tail[1];
      vector={signature:'()',calldata:[],failure,expectedBytes:payload?revertBytes(payload):[]};
    } else [vector]=semanticVectors({...fixture,expectations:[call[1]+' '+call[4]]},abi);
    if(vector.signature==='constructor'&&vectors.length) throw new HostLimit('redeployment is not adapted');
    vectors.push({...vector,value:value.toString()});ordered.push({kind:'call',lineIndex,original,vector:vectors.length-1});
  }
  if(!vectors.length) throw new HostLimit('no payment vectors');
  return {vectors,gas,ordered};
}
function self(n) {
  if(n?.nodeType==='Identifier'&&n.name==='this') return true;
  return n?.nodeType==='FunctionCall'&&n.kind==='typeConversion'&&
    n.expression?.nodeType==='ElementaryTypeNameExpression'&&n.expression.typeName?.name==='address'&&
    n.arguments?.length===1&&self(n.arguments[0]);
}
export function unsupportedPaymentHost(n) {
  if(!n||typeof n!=='object') return false;
  if(n.nodeType==='InlineAssembly') return true;
  if(n.nodeType==='MemberAccess') {
    if(['block','tx'].includes(n.expression?.name)) return true;
    if(n.expression?.name==='msg'&&n.memberName!=='value') return true;
    if(['code','codehash'].includes(n.memberName)||n.memberName==='balance'&&!self(n.expression)) return true;
  }
  if(n.nodeType==='FunctionCall') {
    if(['gasleft','blockhash','blobhash','selfdestruct'].includes(n.expression?.name)) return true;
    const t=n.expression?.typeDescriptions?.typeIdentifier??'';
    if(/t_function_(?:external|barecall|delegatecall|baredelegatecall|staticcall|barestaticcall)/.test(t)) return true;
  }
  return Object.values(n).some(v=>Array.isArray(v)?v.some(unsupportedPaymentHost):unsupportedPaymentHost(v));
}
export async function replayPayments(artifact,vectors) {
  const vm=await machine();let frames=[],active=[],deposits=0n,unsupportedCreate=false;
  vm.evm.events.on('beforeMessage',m=>{const f={depth:m.depth,to:m.to?.toString()??null,caller:m.caller.toString(),
    value:m.value.toString(),data:bytesToHex(m.data),gasLimit:m.gasLimit.toString(),steps:0};frames.push(f);active.push(f);});
  vm.evm.events.on('step',()=>{if(active.length)active.at(-1).steps++;});
  vm.evm.events.on('afterMessage',r=>{const f=active.pop();if(f){f.exception=r.execResult.exceptionError?.error??null;
    if(f.to===null&&r.execResult.exceptionError&&r.execResult.returnValue.length)unsupportedCreate=true;
    f.returnData=bytesToHex(r.execResult.returnValue);f.createdAddress=r.createdAddress?.toString()??null;
    if(r.createdAddress&&!r.execResult.exceptionError){f.runtimeCodeSha256=sha(r.execResult.returnValue);f.runtimeCodeBytes=r.execResult.returnValue.length;}}
    if(r.createdAddress&&!r.execResult.exceptionError) deposits+=BigInt(r.execResult.returnValue.length)*HOST_GAS.code;});
  const observed=[];let address,failedDeployment=false,deployment;
  async function execute(data,ctor,value,signature) {
    frames=[];active=[];deposits=0n;unsupportedCreate=false;
    const intrinsic=hostGas(data,ctor,0n,0n,0n).intrinsic;
    if(BigInt(intrinsic)>=INITIAL_GAS) throw new HostLimit('intrinsic consumes unchanged host gas allowance');
    const {result,metrics}=await vm.call({...(ctor?{}:{to:address}),data,value:BigInt(value),gasLimit:INITIAL_GAS-BigInt(intrinsic)});
    if(unsupportedCreate)throw new HostLimit('pinned-host gas on failed creation with return data is not adapted');
    const actual=ctor?creationObservation(result.execResult,signature,metrics):observation(result.execResult,signature,metrics);
    return {result,actual:{...actual,value,frames,hostGas:hostGas(data,ctor,result.execResult.executionGasUsed,
      result.execResult.gasRefund??0n,deposits)}};
  }
  for(const vector of vectors) {
    try {
      if(failedDeployment) throw new HostLimit('calls after failed deployment are not adapted');
      const ctor=vector.signature==='constructor';
      if(!address&&!ctor) {
        const d=await execute(hexToBytes('0x'+artifact.evm.bytecode.object),true,'0','constructor');
        deployment=d.actual;if(d.actual.failed||!d.result.createdAddress) throw new HostLimit('default deployment failed');
        address=d.result.createdAddress;
      }
      const selector=ctor||vector.signature==='()'?'':artifact.evm.methodIdentifiers[vector.signature];
      if(selector===undefined) throw new HostLimit('unknown ABI method identifier');
      const args=vector.calldata?hex(vector.calldata).slice(2):(vector.args??[]).map(word).join('');
      const data=hexToBytes('0x'+(ctor?artifact.evm.bytecode.object:selector)+args);
      const {result,actual}=await execute(data,ctor,vector.value??'0',vector.signature);observed.push(actual);
      const expectedBytes=vector.failure?(vector.revertBytes??vector.expectedBytes??[]):vector.expectedBytes;
      if(actual.failed!==vector.failure||(expectedBytes!==undefined?actual.returnData!==hex(expectedBytes):
          JSON.stringify(actual.values)!==JSON.stringify(vector.expected)))
        return {status:'broken',reason:'exact payment observation mismatch',observed,deployment,expected:vector};
      if(ctor){address=result.createdAddress;failedDeployment=actual.failed;if(!actual.failed&&!address)throw new HostLimit('creation returned no address');}
    }catch(e){return {status:'blocked',reason:e.message,observed,deployment,blockedVector:vector};}
  }
  return {status:'working',reason:'all payment vectors match actual bytecode execution',observed,deployment};
}
export async function runPaymentFixture(path,directory,compile) {
  const sourceBytes=readFileSync(join(directory,path));const fixture=parseFixture(new TextDecoder('utf-8',{fatal:true}).decode(sourceBytes));
  if(fixture.sources.size!==1||Object.keys(fixture.settings).some(k=>!['EVMVersion','compileViaYul','revertStrings'].includes(k))||
      !evmCompatible(fixture.settings.EVMVersion)||fixture.settings.revertStrings&&!['debug','default'].includes(fixture.settings.revertStrings))
    throw new HostLimit('unsupported payment fixture settings');
  const requiredPipelines=runtimePipelines(fixture.settings);const variants=[];let parsed;
  const profiles=[...requiredPipelines];
  for(let index=0;index<profiles.length;index++) {
    const profile=profiles[index];
    try {
      const settings={viaIR:profile==='viaIR'||profile==='irOptimized',evmVersion:'osaka',
        optimizer:{enabled:profile.endsWith('Optimized'),runs:200},metadata:{appendCBOR:false,bytecodeHash:'none'},
        ...(fixture.settings.revertStrings?{debug:{revertStrings:fixture.settings.revertStrings}}:{}),
        outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers']}}};
      const sources=Object.fromEntries([...fixture.sources].map(([n,s])=>[n,{content:withPreamble(s)}]));const input={language:'Solidity',sources,settings};
      const out=compile(input);const errors=(out.errors??[]).filter(e=>e.severity==='error');if(errors.length)throw new HostLimit('reference compiler error: '+JSON.stringify(errors));
      const ast=out.sources[fixture.mainSource].ast;if(unsupportedPaymentHost(ast))throw new HostLimit('unconfigured non-payment host behavior');
      const contract=ast.nodes.filter(n=>n.nodeType==='ContractDefinition'&&n.contractKind==='contract'&&!n.abstract).at(-1)?.name;
      if(!contract)throw new HostLimit('no concrete deployment contract');const artifact=out.contracts[fixture.mainSource][contract];
      parsed??=paymentVectors(fixture,artifact.abi);for(const gas of parsed.gas)if(!profiles.includes(gas.profile))profiles.push(gas.profile);
      const replay=await replayPayments(artifact,parsed.vectors);const gasObserved=[];
      for(const g of parsed.gas.filter(g=>g.profile===profile)) {
        const receipt=replay.observed[g.vector];if(!receipt){if(replay.status!=='broken'){replay.status='blocked';replay.reason='gas vector did not execute';}break;}
        const actual=g.code?receipt.hostGas.codeDeposit:receipt.hostGas.nonCode;
        gasObserved.push({...g,actual,matches:actual===g.expected});
        if(actual!==g.expected){replay.status='broken';replay.reason='exact pinned-host gas mismatch';}
      }
      variants.push({profile,contract,settings,inputSha256:sha(JSON.stringify(input)),
        creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),
        runtimeSha256:sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex')),
        compiledContracts:Object.fromEntries(Object.entries(out.contracts[fixture.mainSource]).map(([name,a])=>[name,{runtimeSha256:sha(Buffer.from(a.evm.deployedBytecode.object,'hex')),runtimeBytes:a.evm.deployedBytecode.object.length/2}])),...replay,gasObserved});
    }catch(e){variants.push({profile,status:'blocked',reason:e.message});}
  }
  return {path,stage:'evm-payment-reference',sourceSha256:sha(sourceBytes),requiredPipelines,requiredProfiles:profiles,
    expectedObservations:fixture.expectations,orderedObservations:parsed?.ordered,variants,
    status:variants.some(v=>v.status==='broken')?'broken':variants.length===profiles.length&&variants.every(v=>v.status==='working')?'working':'blocked'};
}
async function main(args) {
  const options={};for(let i=0;i<args.length;i+=2){if(!['--compiler','--filter','--out'].includes(args[i])||!args[i+1])throw new Error('compiler, exact filter, out required');options[args[i].slice(2)]=args[i+1];}
  if(!options.compiler||!options.filter||!options.out)throw new Error('compiler, exact filter, out required');
  if(sha(readFileSync(options.compiler))!==COMPILER_SHA)throw new Error('compiler SHA mismatch');const solc=createRequire(import.meta.url)(resolve(options.compiler));
  if(solc.cwrap('solidity_version','string',[])()!=='0.8.38+commit.1835d247.Emscripten.clang')throw new Error('compiler version mismatch');
  const c=solc.cwrap('solidity_compile','string',['string','number','number']);const directory=mkdtempSync(join(ROOT,'.lake/upstream/payment-reference-'));let manifest,result;
  try {({manifest}=verifySnapshot(directory));if(!manifest.files.some(f=>f.path===options.filter&&f.path.startsWith('test/libsolidity/semanticTests/')&&f.path.endsWith('.sol')))throw new Error('exact pinned semantic path required');
    try{result=await runPaymentFixture(options.filter,directory,input=>JSON.parse(c(JSON.stringify(input),0,0)));}catch(e){result={path:options.filter,stage:'evm-payment-reference',status:'blocked',reason:e.message};}
  }finally{rmSync(directory,{recursive:true,force:true});}
  const report={metadata:{commit:PIN,compilerSha256:COMPILER_SHA,archiveSha256:manifest.archiveSha256,
    runnerSha256:sha(readFileSync(fileURLToPath(import.meta.url))),adapterSha256:sha(readFileSync(new URL('../solidity-upstream.mjs',import.meta.url))),baseEngineSha256:sha(readFileSync(new URL('./replay.mjs',import.meta.url))),
    dependencyLockSha256:sha(readFileSync(new URL('./package-lock.json',import.meta.url))),initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,
    scope:'Actual pinned-bytecode payment/value/revert/gas observations only. No Lean coverage or compiler correctness theorem; core/callback/profile unchanged.'},result};
  mkdirSync(dirname(resolve(options.out)),{recursive:true});writeFileSync(options.out,JSON.stringify(report,null,2)+'\n');console.log(result.path+': '+result.status);process.exitCode=result.status==='working'?0:1;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url))main(process.argv.slice(2)).catch(e=>{console.error(e);process.exitCode=2;});
