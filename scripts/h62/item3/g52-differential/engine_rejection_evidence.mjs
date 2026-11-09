/** Guarded regression: empty/forged rejection witnesses, unrelated prefixes,
 * substituted transaction facts, fractional gas and malformed logs must not
 * qualify captured reference artifacts. No VM execution occurs in this checker.
 * Caller must independently archive-bind the original records and receipt/code
 * resources; standalone evidence checks grant no coverage or Source agreement.
 * Unattributed diagnostic/stage families and decode failures stay unqualified.
 */
import {readFileSync} from 'node:fs';import {createRequire} from 'node:module';
import {fileURLToPath,pathToFileURL} from 'node:url';import {resolve} from 'node:path';
import {isDeepStrictEqual} from 'node:util';
import {convertExpectedInvalidEngineFixture,executeExpectedInvalidEngineFixture} from './engine_rejection_reference.mjs';
import {classifyBlockRejection} from './eest_rejection.mjs';
import {EngineXAllocations} from './engine_x_allocation.mjs';
const requireCondition=(ok,message)=>{if(!ok)throw new Error(message);};
const equal=(a,b,message)=>requireCondition(isDeepStrictEqual(a,b),message);
const keys=(object,names,message)=>equal(Object.keys(object??{}).sort(),names.split(',').sort(),message);
const bytes=x=>typeof x==='string'&&/^0x(?:[0-9a-f]{2})*$/.test(x);
const sourceNat=x=>{requireCondition(typeof x==='string'&&/^0x[0-9a-f]+$/.test(x),'noncanonical input quantity');return BigInt(x);};
export function exactNat(value) {
 if(typeof value==='number'&&Number.isSafeInteger(value)&&value>=0)return BigInt(value);
 if(typeof value==='string'&&/^(0|[1-9][0-9]*)$/.test(value))return BigInt(value);
 throw new Error('noncanonical integer observation');
}
export function validateAcceptedBlock(block,payload,transactions,m) {
 keys(block,'number,hash,state_root,gas_used,transactions','accepted block schema');
 requireCondition(block?.hash===payload.blockHash&&block.state_root===payload.stateRoot&&exactNat(block.number)===sourceNat(payload.blockNumber)&&exactNat(block.gas_used)===sourceNat(payload.gasUsed),'accepted block commitment mismatch');
 requireCondition(Array.isArray(block.transactions)&&block.transactions.length===transactions.length&&transactions.length===payload.transactions.length,'accepted transaction cardinality');
 let cumulative=0n,logs=0;
 for(const [i,tx] of block.transactions.entries()) {
  const input=transactions[i];
  keys(tx,'index,hash,type,output,execution_exception,logs,receipt_status,receipt_cumulative_gas_used,total_gas_spent,execution_gas_used,native_gas_refund_counter,gas_limit','native transaction schema');
  requireCondition(Number.isSafeInteger(tx.index)&&tx.index===i&&Number.isSafeInteger(tx.type)&&tx.type===input.type&&tx.hash===m.bytesToHex(input.hash())&&exactNat(tx.gas_limit)===input.gasLimit,'transaction identity differs from input bytes');
  const spent=exactNat(tx.total_gas_spent);cumulative+=spent;
  requireCondition(spent<=input.gasLimit&&exactNat(tx.receipt_cumulative_gas_used)===cumulative&&exactNat(tx.execution_gas_used)<=input.gasLimit,'transaction gas inconsistency');
  exactNat(tx.native_gas_refund_counter);
  requireCondition(bytes(tx.output)&&(tx.execution_exception===null||(typeof tx.execution_exception==='string'&&tx.execution_exception.length>0))&&Number.isSafeInteger(tx.receipt_status)&&tx.receipt_status===(tx.execution_exception?0:1),'transaction output/exception/status shape');
  requireCondition(Array.isArray(tx.logs)&&(!tx.execution_exception||tx.logs.length===0),'malformed or reverted transaction logs');
  for(const log of tx.logs)requireCondition(log&&isDeepStrictEqual(Object.keys(log).sort(),['address','data','topics'])&&typeof log.address==='string'&&/^0x[0-9a-f]{40}$/.test(log.address)&&Array.isArray(log.topics)&&log.topics.length<=4&&log.topics.every(x=>typeof x==='string'&&/^0x[0-9a-f]{64}$/.test(x))&&bytes(log.data),'malformed native log entry');
  logs+=tx.logs.length;
 }
 requireCondition(cumulative===exactNat(block.gas_used),'accepted block cumulative gas mismatch');
 return {transactions:transactions.length,logs};
}
export function validateRejectionFacts(rejection,transactions,m) {
 keys(rejection,'status,fields,actual_categories,matched_categories,block_index,expected_exception,engine_reason,validation_facts,before_state_root,after_state_root,before_head,after_head','rejection schema');
 const facts=rejection.validation_facts,message=rejection.engine_reason;
 requireCondition(facts&&typeof message==='string'&&['provider-validation','runBlock'].includes(facts.stage),'invalid rejection validation stage');
 const expected={stage:facts.stage};
 const wrapped=/^invalid transactions: errors at tx ([0-9]+):/.exec(message);
 const described=/tx type=([0-9]+) hash=(0x[0-9a-f]{64})/.exec(message);
 let tx;
 if(wrapped){requireCondition(facts.stage==='provider-validation','wrapped transaction diagnostic at wrong stage');const index=Number(wrapped[1]);requireCondition(Number.isSafeInteger(index)&&index<transactions.length,'rejection transaction index outside input');tx=transactions[index];}
 else if(described){requireCondition(facts.stage==='runBlock','execution transaction diagnostic at wrong stage');tx=transactions.find(x=>x.type===Number(described[1])&&m.bytesToHex(x.hash())===described[2]);requireCondition(tx!==undefined,'rejection diagnostic transaction not in input');}
 else {
  requireCondition(facts.stage==='provider-validation'&&/^expected blob gas: [0-9]+, got: [0-9]+$/.test(message),'unattributed diagnostic/stage family remains unqualified');
  requireCondition(facts.transactionType===undefined,'header rejection carries unrelated transaction facts');
 }
 if(tx) {
  expected.transactionType=tx.type;
  if(message.startsWith('INTRINSIC_GAS_TOO_LOW:')||/^invalid transactions: errors at tx [0-9]+: gasLimit is too low\./.test(message)) {
   expected.gasLimit=tx.gasLimit.toString();expected.intrinsicGas=tx.getIntrinsicGas().toString();expected.floorGas=m.getCalldataFloorGas(tx,tx.getSenderAddress()).toString();
  }
 }
 equal(facts,expected,'rejection facts differ from decoded input transaction');
 const classified=classifyBlockRejection(rejection.expected_exception,message,expected,rejection.before_state_root,rejection.after_state_root,rejection.before_head,rejection.after_head);
 requireCondition(classified.status==='reference_match','native rejection diagnostic/category or rollback mismatch');
 for(const key of ['status','fields','actual_categories','matched_categories'])equal(rejection[key],classified[key],'rejection classification field mismatch: '+key);
}
export async function validateNativeMatch(record,row,m) {
 requireCondition(row?.status==='payload_rejection_reference_match','nonmatch artifacts are not qualified');
 keys(row,'index,path,case,engine_rpc_complete,forkchoice_executed,source_semantics,differential_complete,binding,expected,native,status,allocation_binding,coverage_admitted,source_matches','matched row schema');
 requireCondition(row.index===record.index&&row.path===record.path&&row.case===record.case,'artifact identity differs from input');
 const converted=await convertExpectedInvalidEngineFixture(record,m);
 requireCondition(converted.status==='converted','original payload cannot be canonically converted');
 const checked=await executeExpectedInvalidEngineFixture(record,m,async()=>row.native);
 requireCondition(checked.status==='payload_rejection_reference_match','incomplete or input-unbound native rejection evidence');
 equal(row.binding,converted.binding,'captured payload binding differs from canonical conversion');equal(row.expected,converted.expected,'captured rejection plan differs from input');
 requireCondition(row.coverage_admitted===false&&row.source_matches===0&&row.engine_rpc_complete===false&&row.forkchoice_executed===false&&row.differential_complete===false&&row.source_semantics==='unsupported-adapter-pending','conflated reference/source flags');
 const native=row.native;keys(native,'status,fields,blocks,rejections,steps,observation_limits,header_validation,block_validation,block_size_validation,max_rlp_block_size,provider_consensus_validation_enabled,consensus_scope,post_state_scope,source_semantics','native match schema');equal(native.fields,[],'native match retains failure fields');
 requireCondition(native.status==='reference_match'&&native.source_semantics==='unsupported-adapter-pending'&&native.header_validation===true&&native.block_validation===true&&native.block_size_validation===true&&native.provider_consensus_validation_enabled===true&&native.max_rlp_block_size===8388608,'missing native validators');
 requireCondition(Number.isSafeInteger(native.steps)&&native.steps>=0&&native.steps<=5000000,'noncanonical/out-of-budget native step observation');
 requireCondition(native.consensus_scope==='NoProof execution/header checks; no beacon consensus, signatures or fork-choice proof'&&native.post_state_scope==='fixture-declared accounts plus validated complete block header commitments','native validation scope mismatch');
 equal(native.observation_limits,['native transaction outputs/logs/gas retained; fixture commits receipts/state but has no direct return/revert-byte expectation','source executable semantics not connected; no isolated per-transaction storage snapshot claim','native_gas_refund_counter is the engine counter, not necessarily the capped applied refund'],'changed observation limits');
 // Same constant-fork decoder settings as the unchanged native block adapter.
 const lastFork=m.Mainnet.hardforks.findIndex(fork=>fork.name===m.Hardfork.Osaka);
 requireCondition(lastFork>=0,'native Osaka decoder parameters missing');
 const hardforks=m.Mainnet.hardforks.slice(0,lastFork+1).map(fork=>({name:fork.name,block:0}));
 const common=m.createCustomCommon({chainId:1,hardforks},m.Mainnet,{hardfork:m.Hardfork.Osaka,eips:[7934],params:{7934:{maxRlpBlockSize:8388608}},customCrypto:{kzg:m.kzg}});
 requireCondition(common.isActivatedEIP(7934)&&common.param('maxRlpBlockSize')===8388608n,'native decoder block-size rule mismatch');
 const blocks=converted.record.fixture.blocks.map(item=>m.createBlockFromRLP(m.hexToBytes(item.rlp),{common}));
 const rejected=new Map(converted.expected.map((x,i)=>[x.block_index,i]));let head=converted.binding.genesis_hash,accepted=0,transactions=0,logs=0;
 for(const [index,item] of record.fixture.engineNewPayloads.entries()) {
  const payload=item.params[0];requireCondition(payload.parentHash===head,'payload history differs from last accepted prefix');
  requireCondition(m.bytesToHex(blocks[index].hash())===payload.blockHash,'decoded block differs from input payload');
  if(rejected.has(index))validateRejectionFacts(native.rejections[rejected.get(index)],blocks[index].transactions,m);
  else {
   const result=validateAcceptedBlock(native.blocks[accepted++],payload,blocks[index].transactions,m);transactions+=result.transactions;logs+=result.logs;head=payload.blockHash;
  }
 }
 requireCondition(record.fixture.lastblockhash===head,'input final head differs from accepted prefix');
 return {index:record.index,qualified_rejections:converted.expected.length,accepted_prefix_blocks:accepted,transaction_observations:transactions,raw_log_entries:logs,steps:native.steps};
}
export async function main(bulk,items) {
 requireCondition(Array.isArray(items)&&items.length>=1&&items.length<=4,'bounded evidence item list required');
 const require=createRequire(resolve(bulk,'reference/package.json')),loaded=[];
 for(const name of ['@ethereumjs/common','@ethereumjs/block','@ethereumjs/util','@ethereumjs/tx','micro-eth-signer/kzg.js','@paulmillr/trusted-setups/fast-peerdas.js'])loaded.push(await import(pathToFileURL(require.resolve(name)).href));
 const m={...loaded[0],...loaded[1],...loaded[2],...loaded[3],kzg:new loaded[4].KZG(loaded[5].trustedSetup)};
 const allocations=new EngineXAllocations(resolve(bulk,'engine-x-allocations.jsonl'),JSON.parse(readFileSync(resolve(bulk,'engine-x-allocations-index.json'),'utf8')));
 try {
  const output=[];
  for(const {record,row} of items){const bound=allocations.bind(record);equal(row.allocation_binding,bound.binding,'captured allocation binding differs from original input');output.push(await validateNativeMatch(bound.record,row,m));}
  return {role:'native-artifact-consistency-only',items:output,new_native_executions:0,source_matches:0,engine_rpc_complete:false,full_conformance:false};
 } finally {allocations.close();}
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url))console.log(JSON.stringify(await main(process.argv[2],JSON.parse(readFileSync(0,'utf8')))));
