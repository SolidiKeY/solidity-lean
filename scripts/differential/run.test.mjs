// Guards against vacuous agreement and silently dropped refusal/mode denominators.
import test from 'node:test';
import assert from 'node:assert/strict';
import {validateRecords,summarize,coverage} from './run.mjs';
import {compare,variants} from '../evm-reference/generated.mjs';
const word = n => BigInt(n).toString(16).padStart(64,'0');
const record = {schema:1,index:0,seed:1108,kind:0,a:'0',b:'1',
  source:'contract Generated {}',expected:{failed:false,storage:['x = 0','y = 1'],revertData:'0x'}};
const actual = () => ({run:{failed:false,returnData:'0x'+word(0)+word(1)},
  storage:{failed:false,returnData:'0x'+word(0)+word(1)},rawStorage:['0','1']});
test('all modelled fields detect mutations including post-revert storage',()=>{
  assert.equal(compare(record,actual()),true);
  for (const mutate of [a=>{a.run.failed=true;},a=>{a.run.returnData='0x';},
    a=>{a.storage.failed=true;},a=>{a.storage.returnData='0x';},a=>{a.rawStorage[0]='2';}]) {
    const a=actual();mutate(a);assert.equal(compare(record,a),false);
  }
  const reverted={...record,expected:{...record.expected,failed:true,revertData:'0x'}};
  const a=actual();a.run={failed:true,returnData:'0x',exception:'revert'};
  assert.equal(compare(reverted,a),true);
  a.rawStorage[0]='7';assert.equal(compare(reverted,a),false);
  a.rawStorage[0]='0';a.run.exception='out of gas';assert.equal(compare(reverted,a),false);
});
test('panic payload bytes are compared exactly',()=>{
  const panic='0x4e487b71'+word(0x11);
  const r={...record,expected:{...record.expected,failed:true,revertData:panic}};
  const a=actual();a.run={failed:true,exception:'revert',returnData:panic};
  assert.equal(compare(r,a),true);
  a.run.returnData='0x4e487b71'+word(0x12);assert.equal(compare(r,a),false);
});
test('missing, duplicate and empty matrices cannot pass',()=>{
  const row={record,variants:variants.map(variant=>({variant,status:'agree'}))};
  assert.equal(summarize([row],1).modes['legacy-off'].agree,1);
  assert.throws(()=>summarize([],0));
  assert.throws(()=>summarize([row],2));
  assert.throws(()=>summarize([{...row,variants:row.variants.slice(1)}],1));
  assert.throws(()=>summarize([{...row,variants:row.variants.map(()=>row.variants[0])}],1));
});
test('refusals remain visible and malformed generator output is rejected',()=>{
  validateRecords([record],1,1108);
  assert.throws(()=>validateRecords([],1,1108));
  assert.throws(()=>validateRecords([{...record,index:1}],1,1108));
  assert.throws(()=>validateRecords([{...record,a:'-1'}],1,1108));
  const refusal={index:0,seed:1108,refusal:'unsupported statement'};
  validateRecords([refusal],1,1108);
  const s=summarize([{record:refusal,variants:[]}],1);
  assert.equal(s.refused,1);assert.equal(s.admitted,0);
});

test('coverage separates both operand boundaries and outcomes by family',()=>{
  const f=coverage([record,{...record,index:1,expected:{...record.expected,failed:true}}]);
  assert.deepEqual(f[0],{total:2,success:1,failure:1,aBoundary:2,bBoundary:2});
  assert.equal(f[1].total,0);
});
