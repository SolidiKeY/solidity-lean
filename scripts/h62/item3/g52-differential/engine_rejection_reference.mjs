/** Guarded regression: expected-invalid Engine metadata must never become a
 * positive payload match, an RPC-error pass, or a rejection without native
 * category, rollback and complete prefix evidence. Caller must separately bind
 * the original record to the pinned archive and use the bounded native worker.
 * This partial adapter establishes neither Engine RPC nor Source agreement.
 */
import {convertEngineFixture,engineConversionFailure} from './engine_payload_reference.mjs';
import {encodePayloadForNativeDecode} from './engine_payload_encoding.mjs';
import {classifyBlockRejection} from './eest_rejection.mjs';

const keys=new Set(['forkchoiceUpdatedVersion','newPayloadVersion','params','validationError']);
const category=/^(?:BlockException|TransactionException)\.[A-Z][A-Z0-9_]*(?:\|(?:BlockException|TransactionException)\.[A-Z][A-Z0-9_]*)*$/;
const hash=/^0x[0-9a-f]{64}$/;

export function rejectionPlan(record) {
 const requests=record?.fixture?.engineNewPayloads;
 if(!Array.isArray(requests)||!requests.length)return {status:'unsupported',reason:'missing-rejection-payload-sequence'};
 const expected=[];
 for(const [index,item] of requests.entries()) {
  if(!item||typeof item!=='object'||Array.isArray(item))return {status:'unsupported',reason:'rejection-request-shape'};
  // RPC exceptions cannot be observed by an offline native block validator.
  if(Object.hasOwn(item,'errorCode'))return {status:'unsupported',reason:'engine-rpc-error-expectation-pending'};
  if(Object.keys(item).some(key=>!keys.has(key)))return {status:'unsupported',reason:'unknown-rejection-request-fields'};
  if(Object.hasOwn(item,'validationError')) {
   if(typeof item.validationError!=='string'||!category.test(item.validationError))return {status:'unsupported',reason:'rejection-category-shape'};
   expected.push({block_index:index,expected_exception:item.validationError});
  }
 }
 if(!expected.length)return {status:'unsupported',reason:'no-expected-invalid-payload'};
 // Copy the complete input; remove only metadata after retaining it verbatim.
 const normalized=structuredClone(record);
 for(const item of normalized.fixture.engineNewPayloads)delete item.validationError;
 return {status:'planned',record:normalized,expected};
}

export async function convertExpectedInvalidEngineFixture(record,m) {
 const plan=rejectionPlan(record);
 if(plan.status!=='planned')return plan;
 // Only transport an expected-invalid gas-cap failure; native decode is NOT
 // replaced. The byte provider is serialized here, never sent as a Block to VM.
 let payloadIndex=0;const rawIndices=[];
 const transport={...m,createBlockFromExecutionPayload:async(payload,options)=>{
  const index=payloadIndex++;
  try {return await m.createBlockFromExecutionPayload(payload,options);}
  catch(error) {
   const expected=plan.expected.find(item=>item.block_index===index);
   if(!expected||!expected.expected_exception.split('|').includes('TransactionException.GAS_LIMIT_EXCEEDS_MAXIMUM')||!/^Invalid tx at index [0-9]+: Error: Transaction gas limit [0-9]+ exceeds the maximum allowed by EIP-7825 \([0-9]+\)$/.test(String(error)))throw error;
   const encoded=await encodePayloadForNativeDecode(plan.record.fixture.engineNewPayloads[index],m);
   rawIndices.push(index);
   return {hash:()=>m.hexToBytes(encoded.block_hash),serialize:()=>m.hexToBytes(encoded.rlp),transactions:[]};
  }
 }};
 const converted=await convertEngineFixture(plan.record,transport);
 if(converted.status!=='converted')return converted;
 if(rawIndices.length)converted.binding.raw_payload_indices=rawIndices;
 for(const item of plan.expected)converted.record.fixture.blocks[item.block_index].expectException=item.expected_exception;
 return {...converted,expected:plan.expected};
}

export async function executeExpectedInvalidEngineFixture(record,m,execute) {
 const limits={engine_rpc_complete:false,forkchoice_executed:false,source_semantics:'unsupported-adapter-pending',differential_complete:false};
 try {
  const converted=await convertExpectedInvalidEngineFixture(record,m);
  if(converted.status!=='converted')return {...converted,...limits};
  const native=await execute(converted.record);
  const base={...limits,binding:converted.binding,expected:converted.expected,native};
  if(native?.status==='reference_mismatch')return {...base,status:'payload_rejection_mismatch'};
  if(native?.status==='unsupported')return {...base,status:'engine_error',retryable:true,reason:'native-rejection-unsupported'};
  if(native?.status!=='reference_match')return {...base,status:'engine_error',retryable:true,reason:'native-rejection-execution-failed'};
  if(!Array.isArray(native.rejections)||native.rejections.length!==converted.expected.length||!Array.isArray(native.blocks))throw new Error('incomplete rejection/prefix evidence');
  for(const [i,expected] of converted.expected.entries()) {
   const r=native.rejections[i];
   if(!r||r.status!=='reference_match'||r.block_index!==expected.block_index||r.expected_exception!==expected.expected_exception||typeof r.engine_reason!=='string'||!r.validation_facts||![r.before_state_root,r.after_state_root,r.before_head,r.after_head].every(x=>typeof x==='string'&&hash.test(x)))throw new Error('rejection identity/observation mismatch');
   const classified=classifyBlockRejection(expected.expected_exception,r.engine_reason,r.validation_facts,r.before_state_root,r.after_state_root,r.before_head,r.after_head);
   if(classified.status!=='reference_match')throw new Error('rejection diagnostic/rollback disagreement');
  }
  const rejected=new Set(converted.expected.map(x=>x.block_index));
  const accepted=converted.binding.payload_block_hashes.filter((_,i)=>!rejected.has(i));
  if(native.blocks.length!==accepted.length||native.blocks.some((block,i)=>block?.hash!==accepted[i]))throw new Error('incomplete accepted payload prefix');
  let head=converted.binding.genesis_hash,root=record.fixture.genesisBlockHeader.stateRoot,acceptedIndex=0,rejectedIndex=0;
  if(!hash.test(head)||typeof root!=='string'||!hash.test(root))throw new Error('missing genesis prefix commitments');
  for(const [index,item] of record.fixture.engineNewPayloads.entries()) {
   if(rejected.has(index)) {
    const r=native.rejections[rejectedIndex++];
    if(r.before_head!==head||r.after_head!==head||r.before_state_root!==root||r.after_state_root!==root)throw new Error('rejection not bound to prior accepted prefix');
   } else {
    const block=native.blocks[acceptedIndex++],expectedRoot=item.params[0].stateRoot;
    if(typeof expectedRoot!=='string'||!hash.test(expectedRoot)||block.state_root!==expectedRoot)throw new Error('accepted prefix state-root disagreement');
    head=block.hash;root=block.state_root;
   }
  }
  return {...base,status:'payload_rejection_reference_match'};
 } catch(error) {
  return {...limits,status:'engine_error',retryable:true,reason:'engine-rejection-conversion-or-evidence-failed',error:String(error),...(engineConversionFailure(error)?{conversion_failure:engineConversionFailure(error)}:{})};
 }
}

export function rejectionExitCode(counts) {
 return counts.payload_rejection_mismatch||counts.engine_error?1:2;
}
