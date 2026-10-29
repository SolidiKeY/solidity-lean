#!/usr/bin/env node
import {libraryTryContext,libraryTryVectorsFixture,linkLibraryObject} from '../library-try-adapter.mjs';
import {creationTryContext} from '../creation-try-adapter.mjs';
import {directSelfTryContext} from '../self-try-adapter.mjs';
/** Optional machine reference, deliberately separate from Lean coverage. */
import {readFileSync, writeFileSync, mkdirSync, mkdtempSync, rmSync} from 'node:fs';
import {dirname, resolve, join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {createEVM} from '@ethereumjs/evm';
import {Common, Mainnet, Hardfork} from '@ethereumjs/common';
import {Account, createAddressFromString, hexToBytes, bytesToHex} from '@ethereumjs/util';
import {COMPILER_SHA, PIN, verifySnapshot, parseFixture, withPreamble,
  runtimePipelines, semanticVectors, evmCompatible} from '../solidity-upstream.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const sha = data => createHash('sha256').update(data).digest('hex');
// Pinned upstream ExecutionFramework.h:275. This is message execution gas,
// not a transaction gas limit with intrinsic gas subtracted.
export const INITIAL_GAS = 100_000_000n;
export const STEP_LIMIT = 5_000_000;
const VERSION = '0.8.38+commit.1835d247.Emscripten.clang';
const caller = createAddressFromString('0x' + '12'.repeat(20));
const word = n => BigInt.asUintN(256, BigInt(n === 'true' ? 1 : n === 'false' ? 0 : n)).toString(16).padStart(64, '0');
export class HostLimit extends Error {}

/** Actual machine errors may be observations; host/instruction limits never are. */
export function observation(exec, signature, metrics) {
  const exception = exec.exceptionError?.error ?? null;
  // Do not silently treat an unknown implementation/configuration exception as
  // Solidity FAILURE. Only these terminal EVM outcomes are currently adapted.
  if (exception && !['revert', 'out of gas', 'stack overflow'].includes(exception))
    throw new HostLimit('unadapted EVM exception: ' + exception);
  const bytes = exec.returnValue;
  if (exec.logs?.length) throw new HostLimit('log observation not adapted');
  if (bytes.length % 32 && !exception) throw new HostLimit('non-word ABI output');
  const values = exception ? [] : Array.from({length:bytes.length / 32}, (_,i) =>
    BigInt(bytesToHex(bytes.slice(i*32,(i+1)*32))).toString());
  return {signature, failed:exception !== null, values, returnData:bytesToHex(bytes),
    exception, gasUsed:exec.executionGasUsed.toString(), ...metrics};
}

// A successful CREATE returns code, not ABI values. A failed CREATE's data
// must survive unchanged, and both cases retain log/error admission checks.
export function creationObservation(exec, signature, metrics) {
  if (exec.exceptionError) return observation(exec, signature, metrics);
  const actual = observation({...exec, returnValue:new Uint8Array()},signature,metrics);
  return {...actual, runtimeCodeSha256:sha(exec.returnValue), runtimeCodeBytes:exec.returnValue.length};
}

export async function machine(stepLimit = STEP_LIMIT, captureCreations = false, captureCalls = false) {
  if (!Number.isSafeInteger(stepLimit) || stepLimit <= 0 || stepLimit > STEP_LIMIT) throw new HostLimit("invalid reference step budget");
  const evm = await createEVM({common:new Common({chain:Mainnet, hardfork:Hardfork.Osaka}),
    // Pinned test/EVMHost.cpp:418-441 deposits returned code without an
    // EIP-170 size check. Match that explicit test-host rule, not mainnet.
    allowUnlimitedContractSize:true, allowUnlimitedInitCodeSize:true});
  await evm.stateManager.putAccount(caller, new Account(0n, 10n**30n));
  let metrics;
  let creations;
  let calls, frames;
  if (captureCalls) {
    evm.events.on('beforeMessage', m => frames.push({to:m.to?.toString()??null,codeAddress:m.to?m.codeAddress.toString():null,
      caller:m.caller.toString(),value:m.value.toString(),delegatecall:!!m.delegatecall,data:bytesToHex(m.data)}));
    evm.events.on('afterMessage', r => calls.push({...frames.pop(),failed:!!r.execResult.exceptionError,returnData:bytesToHex(r.execResult.returnValue)}));
  }
  if (captureCreations) evm.events.on('afterMessage', result => {
    if (result.createdAddress) creations.push({address:result.createdAddress.toString(),
      failed:!!result.execResult.exceptionError,
      ...(result.execResult.exceptionError ? {halt:result.execResult.exceptionError.error,returnData:bytesToHex(result.execResult.returnValue)} :
        {runtimeCodeSha256:sha(result.execResult.returnValue),runtimeCodeBytes:result.execResult.returnValue.length})});
  });
  evm.events.on('step', step => {
    metrics.steps++;
    metrics.maxStack = Math.max(metrics.maxStack, step.stack.length);
    if (metrics.steps > stepLimit) throw new HostLimit('reference instruction budget exhausted');
  });
  return {evm, async call(options) {
    // Each public vector is a fresh transaction frame (pinned EVMHost.cpp:
    // 206-220). Keep storage/accounts; reset only transaction caches/warmth.
    await evm.journal.cleanup();
    evm.stateManager.originalStorageCache.clear();
    for (const address of evm.precompiles.keys()) evm.journal.addAlwaysWarmAddress(address);
    evm.journal.addAlwaysWarmAddress(caller.toString().slice(2));
    if (options.to) evm.journal.addAlwaysWarmAddress(options.to.toString().slice(2));
    metrics = {steps:0, maxStack:0};
    creations = []; calls = []; frames = [];
    const result = await evm.runCall({caller, origin:caller, gasLimit:INITIAL_GAS, ...options});
    return {result, metrics:{...metrics,...(captureCreations ? {creations} : {}),...(captureCalls ? {calls} : {})}};
  }};
}

export async function replayBytecode(artifact, vectors, stepLimit = STEP_LIMIT, hostContext = null, linked = null) {
  const vm = await machine(stepLimit, hostContext?.kind === 'creation-try-source'||!!linked,!!linked);
  let libraryDeployment,linkManifest;
  if(linked){
   try {
    const object=linked.artifact.evm.bytecode.object;
    if(!/^(?:[0-9a-fA-F]{2})+$/.test(object))throw new HostLimit('unresolved library creation bytecode');
    const {result,metrics}=await vm.call({data:hexToBytes('0x'+object)});
    libraryDeployment={...creationObservation(result.execResult,'library '+linked.name,metrics),address:result.createdAddress?.toString()};
    if(libraryDeployment.failed||!result.createdAddress)return {status:'blocked',reason:'actual library deployment failed',libraryDeployment,observed:[]};
    const address=result.createdAddress.toString();
    if(!hostContext?.libraryAddress||BigInt(address).toString()!==hostContext.libraryAddress)
      return {status:'blocked',reason:'linked library context differs from actual deployment',libraryDeployment,linkManifest:null,observed:[]};
    const creation=linkLibraryObject(artifact.evm.bytecode.object,artifact.evm.bytecode.linkReferences,linked.file,linked.name,address);
    const runtime=linkLibraryObject(artifact.evm.deployedBytecode.object,artifact.evm.deployedBytecode.linkReferences,linked.file,linked.name,address);
    linkManifest={file:linked.file,name:linked.name,address,creationReferences:artifact.evm.bytecode.linkReferences,runtimeReferences:artifact.evm.deployedBytecode.linkReferences,creationPositions:creation.positions,runtimePositions:runtime.positions,originalCreationObjectSha256:sha(artifact.evm.bytecode.object),linkedCreationSha256:sha(Buffer.from(creation.object,'hex')),linkedRuntimeTemplateSha256:sha(Buffer.from(runtime.object,'hex'))};
    artifact={...artifact,evm:{...artifact.evm,bytecode:{...artifact.evm.bytecode,object:creation.object},deployedBytecode:{...artifact.evm.deployedBytecode,object:runtime.object}}};
   } catch(e) {return {status:'blocked',reason:e.message,libraryDeployment:libraryDeployment??null,linkManifest:linkManifest??null,observed:[]};}
  }
  const prerequisites=()=>linked?{libraryDeployment,linkManifest}:{};
  const observed = [];
  let address;
  let deployment;
  let deploymentFailed = false;
  for (const vector of vectors) {
    try {
    if (deploymentFailed) throw new HostLimit('calls after failed deployment need empty-code handling');
    const ctor = vector.signature === 'constructor';
    if (!address && !ctor) {
      const {result, metrics} = await vm.call({data:hexToBytes('0x'+artifact.evm.bytecode.object)});
      deployment = {...creationObservation(result.execResult,'constructor',metrics),
        address:result.createdAddress?.toString()};
      if (deployment.exception || !result.createdAddress) return {status:'blocked',reason:'default reference deployment failed: '+(deployment.exception ?? 'no address'),deployment,observed,...prerequisites()};
      address = result.createdAddress;
    }
    if (!ctor && hostContext?.selfAddress && BigInt(address.toString()).toString() !== hostContext.selfAddress)
      throw new HostLimit('self-try context differs from actual reference deployment');
    const selector = ctor ? '' : artifact.evm.methodIdentifiers[vector.signature];
    if (!ctor && !selector) throw new HostLimit('no canonical method identifier: '+vector.signature);
    const raw = Array.isArray(vector.calldata);
    if (raw && !vector.calldata.every(b=>Number.isInteger(b) && b>=0 && b<256))
      throw new HostLimit('invalid raw calldata byte');
    const payload = raw ? Buffer.from(vector.calldata).toString('hex') : vector.args.map(word).join('');
    const data = (ctor ? artifact.evm.bytecode.object : selector) + payload;
    const {result, metrics} = await vm.call({...(ctor ? {} : {to:address}),data:hexToBytes('0x'+data)});
    const actual = ctor ? creationObservation(result.execResult,vector.signature,metrics) :
      observation(result.execResult, vector.signature, metrics);
    observed.push(actual);
    const expectedBytes = raw ? vector.expectedBytes : vector.failure ? (vector.revertBytes ?? []) : null;
    if (expectedBytes && !expectedBytes.every(b=>Number.isInteger(b) && b>=0 && b<256))
      throw new HostLimit('invalid expected ABI byte');
    if (actual.failed !== vector.failure || (expectedBytes ?
        actual.returnData !== '0x'+Buffer.from(expectedBytes).toString('hex') :
        JSON.stringify(actual.values) !== JSON.stringify(vector.expected)))
      return {status:'broken',reason:'machine expectation mismatch',deployment,observed,expected:vector,...prerequisites()};
    if (ctor) {
      deploymentFailed = actual.failed;
      address = result.createdAddress;
      if (!actual.failed && !address) throw new HostLimit('creation returned no address');
    }
    } catch (e) {
      return {status:'blocked',reason:e.message,deployment,observed,blockedVector:vector,...prerequisites()};
    }
  }
  return {status:'working',reason:'all admitted ABI vectors match on pinned reference EVM',deployment,observed,...(linked?{libraryDeployment,linkManifest}:{})};
}

function hasHost(node) {
  if (!node || typeof node !== 'object') return false;
  if (node.nodeType === 'Identifier' && node.name === 'this') return true;
  if (node.nodeType === 'MemberAccess' && (['msg','block','tx'].includes(node.expression?.name) ||
      ['balance','code','codehash'].includes(node.memberName))) return true;
  if (node.nodeType === 'FunctionCall' && node.expression?.nodeType === 'Identifier' && ['gasleft','blockhash','blobhash'].includes(node.expression.name)) return true;
  if (node.nodeType === 'NewExpression' || node.nodeType === 'InlineAssembly' &&
      /"name":"(call|callcode|delegatecall|staticcall|callvalue|create|create2|selfdestruct|selfbalance|extcodesize|extcodehash|extcodecopy|gas|gaslimit|gasprice|timestamp|number|coinbase|origin|caller|address|balance|blockhash|chainid|prevrandao|basefee|blobbasefee|blobhash)"/.test(JSON.stringify(node))) return true;
  if (node.nodeType === 'FunctionCall' && /external|barecall|send|transfer|delegatecall|staticcall/.test(node.expression?.typeDescriptions?.typeIdentifier ?? '')) return true;
  return Object.values(node).some(v=>Array.isArray(v) ? v.some(hasHost) : hasHost(v));
}

export async function runFixture(path, directory, compile) {
  const bytes = readFileSync(join(directory,path));
  const fixture = parseFixture(new TextDecoder('utf-8',{fatal:true}).decode(bytes));
  const result = {path, sourceSha256:sha(bytes), stage:'evm-reference',
    requiredPipelines:runtimePipelines(fixture.settings), variants:[]};
  if (Object.keys(fixture.settings).some(k=>!['EVMVersion','compileViaYul'].includes(k)) ||
      !evmCompatible(fixture.settings.EVMVersion) || fixture.sources.size !== 1)
    throw new HostLimit('unadapted reference fixture settings or sources');
  for (const pipeline of result.requiredPipelines) {
    try {
    const settings = {viaIR:pipeline === 'viaIR',evmVersion:'osaka',optimizer:{enabled:false,runs:200},
      metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.bytecode.linkReferences','evm.deployedBytecode.object','evm.deployedBytecode.linkReferences','evm.methodIdentifiers']}}};
    const sources = Object.fromEntries([...fixture.sources].map(([name,source])=>[name,{content:withPreamble(source)}]));
    const input = {language:'Solidity',sources,settings};
    const out = compile(input);
    const errors = (out.errors ?? []).filter(e=>e.severity === 'error');
    if (errors.length) { result.variants.push({pipeline,status:'blocked',reason:'reference compiler error',errors}); continue; }
    const ast = out.sources[fixture.mainSource].ast;
    const definition = ast.nodes.filter(n=>n.nodeType === 'ContractDefinition' && n.contractKind === 'contract' && !n.abstract).at(-1);
    const hostContext = directSelfTryContext(ast, definition, {referenceOnly:true}) ?? creationTryContext(ast, definition) ?? libraryTryContext(ast, definition);
    if (hasHost(ast) && !hostContext) throw new HostLimit('host-dependent behavior not adapted');
    const contract = definition?.name;
    if (!contract) throw new HostLimit('no concrete deployment contract');
    const artifact = out.contracts[fixture.mainSource][contract];
    const linked=hostContext?.kind==='linked-library-try-source'?{file:fixture.mainSource,name:hostContext.libraryName,artifact:out.contracts[fixture.mainSource][hostContext.libraryName]}:null;
    const vectors = semanticVectors(linked?libraryTryVectorsFixture(fixture,hostContext):fixture, artifact.abi);
    const provenance = {pipeline,contract,settings,...(hostContext ? {hostContext} : {}),inputSha256:sha(JSON.stringify(input)),
      ...(linked?{originalCreationObjectSha256:sha(artifact.evm.bytecode.object)}:{creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),runtimeSha256:sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex'))}), vectors};
    try { result.variants.push({...provenance,...await replayBytecode(artifact,vectors,STEP_LIMIT,hostContext,linked)}); }
    catch (e) { result.variants.push({...provenance,status:'blocked',reason:e.message}); }
    } catch (e) { result.variants.push({pipeline,status:'blocked',reason:e.message}); }
  }
  result.status = result.variants.some(v=>v.status === 'broken') ? 'broken' :
    result.variants.length === result.requiredPipelines.length && result.variants.every(v=>v.status === 'working') ? 'working' : 'blocked';
  return result;
}

async function main(args) {
  const options = {};
  for (let i=0;i<args.length;i+=2) {
    if (!['--compiler','--filter','--out'].includes(args[i]) || !args[i+1]) throw new Error('usage: replay.mjs --compiler FILE --filter EXACT_PATH --out FILE');
    options[args[i].slice(2)] = args[i+1];
  }
  if (!options.compiler || !options.filter || !options.out) throw new Error('compiler, exact filter and output required');
  const compilerBytes = readFileSync(options.compiler);
  if (sha(compilerBytes) !== COMPILER_SHA) throw new Error('compiler SHA mismatch');
  const solc = createRequire(import.meta.url)(resolve(options.compiler));
  if (solc.cwrap('solidity_version','string',[])() !== VERSION) throw new Error('compiler version mismatch');
  const compile = solc.cwrap('solidity_compile','string',['string','number','number']);
  // Extraction must not race the Lean runner's independent SHA verification.
  const directory = mkdtempSync(join(ROOT,'.lake/upstream/evm-source-'));
  let manifest, result;
  try {
  ({manifest} = verifySnapshot(directory));
  if (!manifest.files.some(f=>f.path === options.filter && f.path.startsWith('test/libsolidity/semanticTests/') && f.path.endsWith('.sol')))
    throw new Error('filter must be one exact pinned semantic fixture');
  try {result = await runFixture(options.filter,directory,input=>JSON.parse(compile(JSON.stringify(input),0,0)));}
  catch(e) {result = {path:options.filter,stage:'evm-reference',status:'blocked',reason:e.message};}
  } finally { rmSync(directory,{recursive:true,force:true}); }
  const report = {metadata:{commit:PIN,compiler:VERSION,compilerSha256:COMPILER_SHA,
    archiveSha256:manifest.archiveSha256,runnerSha256:sha(readFileSync(fileURLToPath(import.meta.url))),
    adapterSha256:sha(readFileSync(new URL('../solidity-upstream.mjs',import.meta.url))),
    selfTryAdapterSha256:sha(readFileSync(new URL('../self-try-adapter.mjs',import.meta.url))),
    creationTryAdapterSha256:sha(readFileSync(new URL('../creation-try-adapter.mjs',import.meta.url))),
    libraryTryAdapterSha256:sha(readFileSync(new URL('../library-try-adapter.mjs',import.meta.url))),
    dependencyLockSha256:sha(readFileSync(new URL('package-lock.json',import.meta.url))),
    engine:'@ethereumjs/evm 10.1.3',hardfork:'osaka',
    allowUnlimitedContractSize:true,allowUnlimitedInitCodeSize:true,codeSizeRule:'pinned test/EVMHost.cpp:418-441 (code-deposit gas, no EIP-170 cap)',initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,
    scope:'Compiled bytecode reference observations only; no Lean coverage or universal correctness theorem.'},result};
  mkdirSync(dirname(resolve(options.out)),{recursive:true});
  writeFileSync(options.out,JSON.stringify(report,null,2)+'\n');
  console.log(result.path+': '+result.status);
  process.exitCode = result.status === 'working' ? 0 : 1;
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url))
  main(process.argv.slice(2)).catch(e=>{console.error(e);process.exitCode=2;});
