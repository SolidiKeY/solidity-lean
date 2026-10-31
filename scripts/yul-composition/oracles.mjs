/** Finite external expectations derived from pinned source before execution.
 * CREATE identities are predictions from fixed fresh-machine nonce inputs,
 * never aliases obtained from createdAddress, storage, or getter output. */
import {readFileSync} from 'node:fs';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {isDeepStrictEqual} from 'node:util';
import {createAddressFromString,createContractAddress} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
import {keccak_256} from '../evm-reference/node_modules/@noble/hashes/sha3.js';
import {compareState,validateCapture,validateCallCapture,validateBoundary} from './capture.mjs';
const ROOT=fileURLToPath(new URL('../../',import.meta.url)),sha=b=>createHash('sha256').update(b).digest('hex');
export const LOCAL_CALLER='0x'+'12'.repeat(20);
export function predictedAliases(caller=LOCAL_CALLER) {
 if(!/^0x[0-9a-f]{40}$/.test(caller))throw Error('invalid independent creator input');
 const self=createContractAddress(createAddressFromString(caller),0n).toString();
 return {caller,self,child:createContractAddress(createAddressFromString(self),1n).toString(),child2:createContractAddress(createAddressFromString(self),2n).toString()};
}
/** Salt/initcode are compiler-input receipts fixed before VM execution. */
export function create2Aliases(caller,initcode) {
 const a=predictedAliases(caller);if(typeof initcode!=='string'||!/^0x(?:[0-9a-f]{2})+$/.test(initcode))throw Error('missing CREATE2 initcode input');
 const initHash=Buffer.from(keccak_256(Buffer.from(initcode.slice(2),'hex')));
 for(let salt=0;salt<4;salt++)a['create2:'+salt]='0x'+Buffer.from(keccak_256(Buffer.concat([Buffer.from([255]),Buffer.from(a.self.slice(2),'hex'),Buffer.from(salt.toString(16).padStart(2,'0').padEnd(64,'0'),'hex'),initHash]))).subarray(12).toString('hex');return a;
}
export function compareFinalCleanup(variant,aliases) {
 try {
  const c=variant.postPlanCleanup;validateBoundary(c);const last=variant.observed.at(-1);
  if(c.nextCallOrdinal!==last.transaction+1||!isDeepStrictEqual(c.pre,last.capture.post))throw Error('cleanup phase/pre-state mismatch');
  const deleted=aliases.child2,kept=aliases.child,differences=[];
  if(!isDeepStrictEqual(c.effects.deletedAccounts,[deleted])||!isDeepStrictEqual(c.effects.transientBeforeReset,{}))differences.push('cleanup-effects');
  const before=c.pre[deleted],after=c.post[deleted];if(!before||!after||!c.post[kept])throw Error('missing independently predicted cleanup accounts');
  if(!before.exists||before.balance!=='0'||before.nonce!=='1'||before.code==='0x'||after.exists||after.nonce!=='0'||after.balance!=='0'||after.code!=='0x'||Object.values(after.persistent).some(w=>BigInt(w)!==0n))differences.push('deleted-child-state');
  for(const [address,a]of Object.entries(c.pre))if(address!==deleted) {
   const b=c.post[address];for(const field of ['exists','balance','nonce','code','codeSha256','persistent'])if(!isDeepStrictEqual(a[field],b[field]))differences.push('cleanup-unrelated/'+address+'/'+field);
  }
  for(const a of Object.values(c.post))if(Object.values(a.transient).some(w=>BigInt(w)!==0n))differences.push('cleanup-transient-reset');
  for(const kind of ['deleteAccount','clearStorage','putCode']){const ops=c.operations.filter(o=>o.kind===kind);if(ops.length!==1||ops[0].address!==deleted||kind==='putCode'&&ops[0].value!=='0x')differences.push('cleanup-operation/'+kind);}
  const clears=c.operations.filter(o=>o.kind==='transient.clear');if(clears.length!==1||!isDeepStrictEqual(clears[0].value,c.effects.transientBeforeReset))differences.push('cleanup-clear-payload');
  if(!c.post[kept].exists||c.post[kept].code==='0x')differences.push('old-child-destroyed');
  return{status:differences.length?'mismatch':'match',differences,scope:'Observed host beginFrame cleanup, no extra EVM call or runTx/finalization theorem'};
 }catch(e){return{status:'blocked',reason:e.message};}
}
export const STATE_ORACLE_IDS=['constructor-failure','constructors','memory-storage-logs','mixed-logs','modifiers','new-constructor','try-catch'];
export function checkStateOracles(raw) {
 if(sha(raw)!=='44782a1ec3dc372ee6228df202f0d9f5908350157b9402945bdd25ab839248b3')throw Error('missing/stale state oracle registration');
 const rows=JSON.parse(raw);if(!isDeepStrictEqual(rows.map(r=>r.id).sort(),STATE_ORACLE_IDS))throw Error('missing/duplicate state oracle');return rows;
}
const localRows=()=>checkStateOracles(readFileSync(ROOT+'tests/yul-composition/state-oracles.json','utf8'));
export function compareLocalState(fixture,record) {
 const spec=localRows().find(o=>o.id===fixture.id);if(!spec)return{status:'pending',reason:'no independent state/memory oracle'};
 try {
  if(spec.sourceSha256!==sha(fixture.source))throw Error('stale state oracle source');
  if(spec.phase!==(fixture.deploymentOnly?'deployment':'runtime')||record.phase!==spec.phase||record.executionKind!=='runCall')throw Error('missing/wrong observation phase or execution API');
  const aliases=predictedAliases(),d=record.deploymentCapture;validateCapture(d);
  if(d.transaction!==1||d.request.caller!==aliases.caller||d.request.to!==null||d.frames[0].address!==aliases.self||d.frames[0].createdAddress!==aliases.self)throw Error('wrong predicted deployment identity');
  const capture=spec.phase==='deployment'?d:record.observed?.capture;
  validateCallCapture(capture,record.observed,{transaction:spec.phase==='deployment'?1:2,caller:aliases.caller,to:spec.phase==='deployment'?null:aliases.self,value:'0'});
  if(spec.phase==='runtime') {
   if(record.deployment?.address!==aliases.self||d.frames[0].output.exception!==null||d.post[aliases.self]?.code==='0x'||d.post[aliases.self]?.code!==d.frames[0].output.bytes)throw Error('missing successful runtime installation');
  } else if(record.deployment?.candidateAddress!==aliases.self||record.deployment?.runtimeInstalled!==false)throw Error('missing failed candidate observation');
  return {...compareState(capture,spec.oracle,aliases),scope:'Finite source-derived controlled state/window expectations; no whole-world or source correspondence theorem',phase:spec.phase};
 }catch(e){return{status:'blocked',reason:e.message};}
}
/** Request identity independent of duplicated capture fields. Initcode hash is
 * compiler receipt linkage, not an expected state/address derived from code. */
export function independentRequest(call,reported,creationSha256) {
 if(!call||!Array.isArray(call.calldata)||typeof reported!=='string'||!/^0x(?:[0-9a-f]{2})*$/.test(reported))throw Error('missing/malformed actual request bytes');
 const args=Buffer.from(call.calldata).toString('hex');
 if(!call.constructor) {
  const expected='0x'+Buffer.from(keccak_256(new TextEncoder().encode(call.signature)).slice(0,4)).toString('hex')+args;
  if(reported!==expected)throw Error('request selector/arguments differ from pinned source plan');return expected;
 }
 const bytes=reported.slice(2);
 if(!/^[0-9a-f]{64}$/.test(creationSha256)||bytes.length<args.length||!bytes.endsWith(args))throw Error('missing/wrong compiled initcode or constructor arguments');
 const prefix=args.length?bytes.slice(0,-args.length):bytes;
 if(sha(Buffer.from(prefix,'hex'))!==creationSha256)throw Error('CREATE request initcode differs from compiler receipt');
 return reported;
}
export function checkUpstreamOracles(raw) {
 if(sha(raw)!=='4809f87e1b5915d9c8d6d18ed8520e6d7a6d3be04b516af1837851d84cf7837c')throw Error('missing/stale upstream state oracle registration');
 const rows=JSON.parse(raw),names=["blobhash.sol","blobhash_index_exceeding_blob_count.sol","calldata_array_assign_dynamic.sol","calldata_array_assign_static.sol","calldata_array_read.sol","calldata_assign.sol","calldata_assign_from_nowhere.sol","calldata_length_read.sol","calldata_offset_read.sol","calldata_offset_read_write.sol","calldata_struct_assign.sol","calldata_struct_assign_and_return.sol","chainid.sol","clz.sol","constant_access.sol","constant_access_referencing.sol","external_function_pointer_address.sol","external_function_pointer_address_assignment.sol","external_function_pointer_selector.sol","external_function_pointer_selector_assignment.sol","external_identifier_access_shadowing.sol","for_loop_break.sol","for_loop_continue.sol","for_loop_nested.sol","function_name_clash.sol","inline_assembly_embedded_function_call.sol","inline_assembly_for.sol","inline_assembly_for2.sol","inline_assembly_function_call.sol","inline_assembly_function_call2.sol","inline_assembly_function_call_assignment.sol","inline_assembly_if.sol","inline_assembly_in_modifiers.sol","inline_assembly_memory_access.sol","inline_assembly_read_and_write_stack.sol","inline_assembly_recursion.sol","inline_assembly_storage_access.sol","inline_assembly_storage_access_inside_function.sol","inline_assembly_storage_access_local_var.sol","inline_assembly_storage_access_via_pointer.sol","inline_assembly_switch.sol","inline_assembly_transient_storage_access_inside_function.sol","inline_assembly_write_to_stack.sol","inlineasm_empty_let.sol","keccak256_assembly.sol","keccak256_optimization.sol","keccak256_optimizer_bug_different_memory_location.sol","keccak256_optimizer_cache_bug.sol","keccak_optimization_bug_string.sol","keccak_yul_optimization.sol","leave.sol","mcopy.sol","mcopy_empty.sol","mcopy_overlap.sol","optimize_memory_store_multi_block.sol","optimize_memory_store_multi_block_bugreport.sol","prevrandao.sol","returndatacopy_using_stale_returndatasize.sol","selfbalance.sol","shadowing_local_function_opcode.sol","slot_access.sol","slot_access_via_mapping_pointer.sol","slotnum_pre_amsterdam_function.sol","transient_storage_creation.sol","transient_storage_low_level_calls.sol","transient_storage_multiple_calls_different_transactions.sol","transient_storage_multiple_transactions.sol","transient_storage_reset_between_creation_runtime.sol","transient_storage_sanity_checks.sol","transient_storage_selfdestruct.sol","transient_storage_simple_reentrancy_lock.sol","truefalse.sol","tstore_hidden_staticcall.sol"];
 if(!isDeepStrictEqual(rows.map(r=>r.path.split('/').at(-1)).sort(),names))throw Error('missing/duplicate upstream oracle');return rows;
}

export function compareUpstreamState(fixture,variant,caller) {
 const rows=checkUpstreamOracles(readFileSync(ROOT+'tests/yul-composition/upstream-state-oracles.json','utf8')),spec=rows.find(o=>o.path===fixture.path);
 if(!spec)return{status:'pending',reason:'independent state/memory oracle absent'};
 try {
  if(spec.callPlanSha256!==sha(JSON.stringify(fixture.plan))||spec.sourceSha256!==fixture.sourceSha256||!isDeepStrictEqual(spec.calls.map(o=>o.signature),fixture.plan.calls.map(c=>c.signature)))throw Error('stale source/call oracle');
  if(!Array.isArray(variant.observed))throw Error('missing independent state observations');
  let aliases=predictedAliases(caller);const calls=[];
  if(fixture.path.endsWith('/transient_storage_low_level_calls.sol')) {
   const q=variant.oracleInputs;
   if(!q||q.contract!=='D'||q.inputSha256!==variant.inputSha256||q.initcodeSha256!==sha(Buffer.from(q.create2Initcode?.slice(2)??'','hex'))||q.initcodeSha256!==variant.artifactHashes?.D?.creation||!/^[0-9a-f]{64}$/.test(variant.artifactHashes?.D?.runtime))throw Error('missing/stale CREATE2 compiler inputs');
   aliases=create2Aliases(caller,q.create2Initcode);
  }
  const mapping='0x'+Buffer.from(keccak_256(Buffer.from('0'.repeat(63)+'1'+'0'.repeat(64),'hex'))).toString('hex');
  for(const [i,s]of spec.calls.entries()) {
   try {
   const o=variant.observed[i];if(o.index!==i||o.signature!==s.signature)throw Error('reordered independent state observations');
   const call=fixture.plan.calls[i],transaction=i+(fixture.plan.calls[0].constructor?1:2);
   if(o.transaction!==transaction||o.value!==call.value||o.inputBytes!=='0x'+Buffer.from(call.calldata).toString('hex'))throw Error('wrong call/transaction identity');
   const input=independentRequest(call,o.requestData,variant.creationSha256);
   validateCallCapture(o.capture,o.actual,{transaction,input,value:call.value,caller,to:call.constructor?null:aliases.self});
   const oracle=structuredClone(s.oracle);
   if(fixture.path.endsWith('/transient_storage_low_level_calls.sol')) {
    for(const f of oracle.frames??[])if(f.fields.kind==='create')f.fields.input=variant.oracleInputs.create2Initcode;
    const a=oracle.accounts.find(a=>a.address==='create2:'+i&&a.phase==='post');if(!a)throw Error('missing target expectation');a.fields.codeSha256=variant.artifactHashes.D.runtime;
   }
   for(const e of oracle.slots??[])if(typeof e.value==='string'&&e.value.startsWith('address:')) {
    const value=aliases[e.value.slice(8)];if(!value)throw Error('unknown independent address input');e.value='0x'+BigInt(value).toString(16).padStart(64,'0');
   }
   for(const e of oracle.slots??[])if(e.slot==='mapping1')e.slot=mapping;else if(e.slot==='mapping1next')e.slot='0x'+(BigInt(mapping)+1n).toString(16).padStart(64,'0');
   const value=compareState(o.capture,oracle,aliases);calls.push({index:i,signature:s.signature,...value});
   }catch(e){calls.push({index:i,signature:s.signature,status:'blocked',reason:e.message});}
  }
  if(variant.status!=='working'||variant.observed.length!==spec.calls.length)calls.push({status:'blocked',reason:'incomplete/extra reference observations or execution'});
  const cleanup=fixture.path.endsWith('/transient_storage_selfdestruct.sol')?compareFinalCleanup(variant,aliases):undefined;
  const states=cleanup?[...calls,cleanup]:calls;
  return {...(cleanup?{cleanup}:{}),status:states.some(c=>c.status==='mismatch')?'mismatch':states.some(c=>c.status==='blocked')?'blocked':states.every(c=>c.status==='match')?'match':'pending',scope:'Finite selected source-derived assertions; complete upstream state/world correspondence pending',pendingDomains:spec.pendingDomains??['Untouched/native worlds and source correspondence'],calls};
 }catch(e){return{status:'blocked',reason:e.message};}
}
