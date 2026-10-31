/** Finite external expectations derived from pinned source before execution.
 * CREATE identities are predictions from fixed fresh-machine nonce inputs,
 * never aliases obtained from createdAddress, storage, or getter output. */
import {readFileSync} from 'node:fs';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {isDeepStrictEqual} from 'node:util';
import {createAddressFromString,createContractAddress} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
import {keccak_256} from '../evm-reference/node_modules/@noble/hashes/sha3.js';
import {compareState,validateCapture,validateCallCapture} from './capture.mjs';
const ROOT=fileURLToPath(new URL('../../',import.meta.url)),sha=b=>createHash('sha256').update(b).digest('hex');
export const LOCAL_CALLER='0x'+'12'.repeat(20);
export function predictedAliases(caller=LOCAL_CALLER) {
 if(!/^0x[0-9a-f]{40}$/.test(caller))throw Error('invalid independent creator input');
 const self=createContractAddress(createAddressFromString(caller),0n).toString();
 return {caller,self,child:createContractAddress(createAddressFromString(self),1n).toString()};
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
export function checkUpstreamOracles(raw) {
 if(sha(raw)!=='7d86a43e299005d43c52b5889a79ccb2082c6543eba1bee5ecd91574845df8d5')throw Error('missing/stale upstream state oracle registration');
 const rows=JSON.parse(raw);const names=['inline_assembly_memory_access.sol','optimize_memory_store_multi_block.sol','optimize_memory_store_multi_block_bugreport.sol','slot_access.sol','transient_storage_creation.sol'];
 if(!isDeepStrictEqual(rows.map(r=>r.path.split('/').at(-1)).sort(),names))throw Error('missing/duplicate upstream oracle');return rows;
}
export function compareUpstreamState(fixture,variant,caller) {
 const rows=checkUpstreamOracles(readFileSync(ROOT+'tests/yul-composition/upstream-state-oracles.json','utf8')),spec=rows.find(o=>o.path===fixture.path);
 if(!spec)return{status:'pending',reason:'independent state/memory oracle absent'};
 try {
  if(spec.sourceSha256!==fixture.sourceSha256||!isDeepStrictEqual(spec.calls.map(o=>o.signature),fixture.plan.calls.map(c=>c.signature)))throw Error('stale source/call oracle');
  if(variant.status!=='working')return{status:'blocked',reason:'reference call execution incomplete'};
  if(variant.observed.length!==spec.calls.length)throw Error('missing independent state observations');
  const aliases=predictedAliases(caller),calls=[];
  const mapping='0x'+Buffer.from(keccak_256(Buffer.from('0'.repeat(63)+'1'+'0'.repeat(64),'hex'))).toString('hex');
  for(const [i,s]of spec.calls.entries()) {
   const o=variant.observed[i];if(o.index!==i||o.signature!==s.signature)throw Error('reordered independent state observations');
   const oracle=structuredClone(s.oracle);
   for(const e of oracle.slots??[])if(e.slot==='mapping1')e.slot=mapping;else if(e.slot==='mapping1next')e.slot='0x'+(BigInt(mapping)+1n).toString(16).padStart(64,'0');
   const value=compareState(o.capture,oracle,aliases);calls.push({index:i,signature:s.signature,...value});
  }
  return {status:calls.some(c=>c.status==='mismatch')?'mismatch':calls.some(c=>c.status==='blocked')?'blocked':calls.every(c=>c.status==='match')?'match':'pending',scope:'Finite selected source-derived assertions; complete upstream state/world correspondence pending',calls};
 }catch(e){return{status:'blocked',reason:e.message};}
}
