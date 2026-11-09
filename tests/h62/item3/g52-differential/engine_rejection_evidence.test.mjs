/** Guarded regression: fractions, forged identities/facts and malformed logs
 * cannot become qualified native observations. Synthetic objects exercise only
 * checker contracts; they are not native executions or fixture passes.
 */
import test from 'node:test';import assert from 'node:assert/strict';
import {exactNat,validateAcceptedBlock,validateRejectionFacts} from '../../../../scripts/h62/item3/g52-differential/engine_rejection_evidence.mjs';
const h=n=>'0x'+n.toString(16).padStart(64,'0');
const tx={type:0,gasLimit:100n,hash:()=>h(4),getIntrinsicGas:()=>50n,getSenderAddress:()=>h(1)};
const m={bytesToHex:x=>x,getCalldataFloorGas:()=>60n};
const payload={blockHash:h(2),stateRoot:h(3),blockNumber:'0x1',gasUsed:'0x14',transactions:['0x01']};
const block=()=>({hash:h(2),state_root:h(3),number:'1',gas_used:'20',transactions:[{index:0,hash:h(4),type:0,output:'0x',execution_exception:null,logs:[],receipt_status:1,receipt_cumulative_gas_used:'20',total_gas_spent:'20',execution_gas_used:'10',native_gas_refund_counter:'0',gas_limit:'100'}]});
const rejection=()=>({status:'reference_match',fields:[],actual_categories:['TransactionException.INTRINSIC_GAS_TOO_LOW','TransactionException.INTRINSIC_GAS_BELOW_FLOOR_GAS_COST'],matched_categories:['TransactionException.INTRINSIC_GAS_TOO_LOW'],block_index:0,expected_exception:'TransactionException.INTRINSIC_GAS_TOO_LOW',engine_reason:'invalid transactions: errors at tx 0: gasLimit is too low. The gasLimit is lower than the minimum gas limit of 50 (intrinsic gas 50), the gas limit is: 40 (block number=1)',validation_facts:{stage:'provider-validation',transactionType:0,gasLimit:'40',intrinsicGas:'50',floorGas:'60'},before_state_root:h(1),after_state_root:h(1),before_head:h(0),after_head:h(0)});

test('integer observations require exact canonical naturals',()=>{
 for(const x of [0,2,'0','200'])assert.equal(typeof exactNat(x),'bigint');
 for(const x of [0.5,2.5,-1,NaN,Infinity,true,'01','+1','1.0','0x1',Number.MAX_SAFE_INTEGER+1])assert.throws(()=>exactNat(x),/noncanonical integer/);
});
test('block and transaction identities, gas and output mutations fail',()=>{
 assert.deepEqual(validateAcceptedBlock(block(),payload,[tx],m),{transactions:1,logs:0});
 for(const mutate of [b=>b.number=1.5,b=>b.gas_used=20.5,b=>b.transactions=[],b=>b.transactions[0].hash=h(8),b=>b.transactions[0].gas_limit='101',b=>b.transactions[0].total_gas_spent=20.5,b=>b.transactions[0].receipt_cumulative_gas_used='19',b=>b.transactions[0].receipt_status=0,b=>b.transactions[0].output='garbage',b=>b.transactions[0].native_gas_refund_counter=-1,b=>b.transactions[0].execution_gas_used='101']) {const b=block();mutate(b);assert.throws(()=>validateAcceptedBlock(b,payload,[tx],m));}
});
test('logs require canonical addresses/topics/data and no failed-call retained logs',()=>{
 const log={address:'0x'+'11'.repeat(20),topics:[h(1)],data:'0x1234'};const b=block();b.transactions[0].logs=[log];assert.equal(validateAcceptedBlock(b,payload,[tx],m).logs,1);
 for(const logs of ['garbage',[{...log,address:'0x12'}],[{...log,topics:['0x12']}],[{...log,data:'0x1'}],[{...log,topics:Array(5).fill(h(1))}],[{...log,extra:true}]]){const bad=block();bad.transactions[0].logs=logs;assert.throws(()=>validateAcceptedBlock(bad,payload,[tx],m));}
 b.transactions[0].execution_exception='revert';b.transactions[0].receipt_status=0;assert.throws(()=>validateAcceptedBlock(b,payload,[tx],m));
});
test('native diagnostic facts are derived from the decoded transaction',()=>{
 const low={...tx,gasLimit:40n};validateRejectionFacts(rejection(),[low],m);
 for(const mutate of [r=>r.validation_facts.gasLimit='41',r=>r.validation_facts.intrinsicGas='49',r=>r.validation_facts.floorGas='59',r=>r.validation_facts.transactionType=1,r=>r.validation_facts.stage='decode',r=>r.engine_reason=r.engine_reason.replace('tx 0:','tx 1:'),r=>r.actual_categories=[],r=>r.matched_categories=[],r=>r.after_head=h(9),r=>r.fields=['rejection_category']]){const r=rejection();mutate(r);assert.throws(()=>validateRejectionFacts(r,[low],m));}
});

test('semantic header diagnostics cannot be relabeled as decoding or execution errors',()=>{
 const r={...rejection(),expected_exception:'BlockException.INCORRECT_EXCESS_BLOB_GAS',actual_categories:['BlockException.INCORRECT_EXCESS_BLOB_GAS'],matched_categories:['BlockException.INCORRECT_EXCESS_BLOB_GAS'],engine_reason:'expected blob gas: 0, got: 1',validation_facts:{stage:'provider-validation'}};
 validateRejectionFacts(r,[],m);
 for(const stage of ['decode','runBlock'])assert.throws(()=>validateRejectionFacts({...r,validation_facts:{stage}},[],m));
 assert.throws(()=>validateRejectionFacts({...r,engine_reason:'unattributed diagnostic'},[],m));
});
