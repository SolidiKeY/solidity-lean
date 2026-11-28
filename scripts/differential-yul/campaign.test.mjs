/** Mock transport checks only: these are not Lean/EVM differential evidence. */
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {runCase,summarize,minimize,campaign,stages,validateRow} from './campaign.mjs';
import {generate,sourceFor,reductions} from './generate.mjs';
const hash=s=>createHash('sha256').update(s).digest('hex');
const observation=()=>({failed:false,returnData:'0x',exception:null,storage:['0','0'],slots:['0','1'],calldata:'0x12345678'});
const artifact=()=>({ir:'exact unoptimized IR',irOptimized:'exact optimized IR',
  storageLayout:{storage:[{label:'x',slot:'0',offset:0,type:'t'},{label:'y',slot:'1',offset:0,type:'t'}],
    types:{t:{label:'uint256',encoding:'inplace',numberOfBytes:'32'}}},
  evm:{bytecode:{object:'6000'},deployedBytecode:{object:'00'},methodIdentifiers:{'run()':'12345678'}}});
const compile=()=>({contracts:{'generated.sol':{Generated:artifact()}}});
const row=(record,statuses=['agree','agree'])=>({index:record.index,sourceSha256:hash(record.source),optimizer:true,
  reference:observation(),results:stages.map((stage,i)=>({stage,status:statuses[i],lean:observation(),...(statuses[i]==='blocked'?{phase:'lean',reason:'fuel exhausted'}:{})}))});
const shrinkRecord=()=>{const r={index:0,seed:1,family:'loop',a:'8',b:'4',rounds:2};return {...r,source:sourceFor(r)};};
function mismatch(record,{stage='ir',field='returnData'}={}) {
  const r=row(record);const result=r.results.find(x=>x.stage===stage);result.status='mismatch';
  result.lean[field]=field==='returnData'?'0x01':field==='storage'?['1','0']:true;
  return r;
}

test('both exact IR stages share one compilation and one reference observation', async()=>{
  const record=generate(1)[0],requests=[];let compilations=0,references=0;
  const r=await runCase(record,{optimizer:false,compile:input=>{
    compilations++;assert.equal(input.sources['generated.sol'].content,record.source);
    assert.equal(input.settings.optimizer.enabled,false);return compile();
  },reference:async a=>{references++;assert.deepEqual(a,artifact());return observation();},lean:async request=>{
    requests.push(request);return {status:'ok',observation:observation()};
  }});
  assert.equal(compilations,1);assert.equal(references,1);
  assert.deepEqual(r.results.map(x=>x.status),['agree','agree']);
  assert.deepEqual(requests.map(x=>x.ir),[artifact().ir,artifact().irOptimized]);
  for (const [i,request] of requests.entries()) {
    assert.equal(request.stage,stages[i]);assert.equal(request.irSha256,hash(request.ir));
    assert.equal(request.sourceSha256,hash(record.source));assert.equal(request.calldata,observation().calldata);
    assert.deepEqual(request.initialStorage,['0','0']);assert.deepEqual(request.slots,['0','1']);
  }
});

test('Lean refusal, fuel, crash, malformed envelopes and observations fail closed',async()=>{
  for (const lean of [async()=>({status:'blocked',reason:'fuel exhausted'}),async()=>{throw Error('transport crash');},
    async()=>({status:'timeout'}),async()=>({status:'blocked',reason:''}),async()=>undefined,
    async()=>({status:'ok',observation:{...observation(),storage:[]}}),
    async()=>({status:'ok',observation:{...observation(),slots:['1','0']}}),
    async()=>({status:'ok',observation:{...observation(),returnData:'0x1'}})]) {
    const r=await runCase(generate(1)[0],{compile,reference:async()=>observation(),lean});
    assert.deepEqual(r.results.map(x=>[x.status,x.phase]),[['blocked','lean'],['blocked','lean']]);
    assert.ok(r.results.every(x=>typeof x.reason==='string'&&x.reason.length));
  }
});

test('reference errors block both stages before Lean executes',async()=>{
  for (const reference of [async()=>{throw Error('engine limit');},async()=>({...observation(),storage:[]}),
    async()=>({...observation(),failed:true,exception:'out of gas'})]) {
    let calls=0;
    const r=await runCase(generate(1)[0],{compile,reference,lean:async()=>{calls++;}});
    assert.equal(calls,0);assert.deepEqual(r.results.map(x=>[x.status,x.phase]),[['blocked','reference'],['blocked','reference']]);
  }
  const record=generate(1)[0];
  await assert.rejects(runCase({...record,source:'other'},{compile,lean:async()=>{}}),/record\/source mismatch/);
  await assert.rejects(runCase(record,{compile}),/missing execution endpoint/);
});

test('summary keeps blocked programs in denominator and requires order, uniqueness and all stages',()=>{
  const records=generate(3),rows=records.map(r=>row(r));
  rows[1].results[0].status='blocked';rows[2].results[1].status='mismatch';
  assert.deepEqual(summarize(rows,3),{requested:3,executedPrograms:2,agreeingPrograms:1,
    stages:{ir:{agree:2,mismatch:0,blocked:1},irOptimized:{agree:2,mismatch:1,blocked:0}}});
  assert.throws(()=>summarize(rows,4),/incomplete/);assert.throws(()=>summarize([],0),/incomplete/);
  for (const alter of [r=>r.reverse(),r=>r[1].index=0,r=>r[1].sourceSha256=r[0].sourceSha256,
    r=>r[0].sourceSha256='bad',r=>r[0].results.pop(),r=>r[0].results.reverse(),
    r=>r[0].results[1].stage='ir',r=>r[0].results[0].status='timeout']) {
    const invalid=structuredClone(rows);alter(invalid);assert.throws(()=>summarize(invalid,3));
  }
});

test('campaign awaits sink and aborts on sink failure without executing next record',async()=>{
  const events=[];
  await assert.rejects(campaign({count:3,execute:async record=>{events.push('execute '+record.index);return row(record);},
    sink:async({record})=>{events.push('sink '+record.index);await Promise.resolve();throw Error('disk full');}}),/disk full/);
  assert.deepEqual(events,['execute 0','sink 0']);
  let saved=0;
  await assert.rejects(campaign({count:1,execute:async r=>({...row(r),index:4}),sink:async()=>{saved++;}}));
  assert.equal(saved,0);
  const ok=await campaign({count:2,execute:async r=>row(r),sink:async()=>{saved++;}});
  assert.equal(saved,2);assert.equal(ok.summary.executedPrograms,2);
});

test('shrinking refuses blocked candidates, changed mismatch fields and changed IR stage',async()=>{
  const record=shrinkRecord(),original=mismatch(record);
  for (const [execute,blocked] of [[async r=>row(r,['blocked','blocked']),true],[async r=>mismatch(r,{field:'storage'}),false],
    [async r=>mismatch(r,{stage:'irOptimized'}),false]]) {
    const minimized=await minimize(record,original,execute);
    assert.deepEqual(minimized.record,record);assert.equal(minimized.complete,!blocked);
    assert.equal(minimized.blockedAttempts,blocked?reductions(record).length:0);
    assert.equal(minimized.unresolvedCandidates,blocked?reductions(record).length:0);
    assert.equal(minimized.attempts,reductions(record).length);assert.equal(minimized.fields,'returnData');
    assert.equal(minimized.stage,'ir');
  }
});

test('shrinking descends strictly and marks budget exhaustion incomplete',async()=>{
  const record=shrinkRecord(),original=mismatch(record),seen=[];
  const execute=async r=>{seen.push(r);assert.equal(r.source,sourceFor(r));return mismatch(r);};
  const limited=await minimize(record,original,execute,{maxAttempts:1});
  assert.equal(limited.attempts,1);assert.equal(limited.complete,false);assert.equal(limited.record.a,'0');
  const minimal=await minimize(record,original,execute);
  assert.deepEqual([minimal.record.a,minimal.record.b,minimal.record.rounds],['0','0',0]);
  assert.equal(minimal.complete,true);assert.equal(minimal.attempts,3);
  await assert.rejects(minimize(record,original,execute,{maxAttempts:0}),/budget/);
  await assert.rejects(minimize(record,row(record),execute),/requires a mismatch/);
  await assert.rejects(minimize(record,original,async()=>{throw Error('endpoint unavailable');}),/endpoint unavailable/);
});


test('row validation rejects stale cached results and forged verdicts',async()=>{
  const record=shrinkRecord(),original=row(record);
  assert.equal(validateRow(record,original),original);
  for (const alter of [r=>r.sourceSha256='0'.repeat(64),r=>r.index++,r=>delete r.optimizer,
    r=>r.results[0].status='mismatch',r=>r.results[0].lean.returnData='0x01',
    r=>r.results[0]={stage:'ir',status:'blocked',phase:'lean',reason:''},
    r=>r.results[0]={stage:'ir',status:'blocked',phase:'unknown',reason:'fuel'}]) {
    const invalid=structuredClone(original);alter(invalid);
    assert.throws(()=>validateRow(record,invalid));
  }
  const oldMismatch=mismatch(record);
  await assert.rejects(minimize(record,oldMismatch,async()=>oldMismatch),/does not match input/);
  let saves=0;
  await assert.rejects(campaign({count:2,execute:async()=>row(generate(1)[0]),sink:async()=>{saves++;}}),/does not match input/);
  assert.equal(saves,1);
});

test('explicit shrink stage preserves that stage and rejects absent or invalid choices',async()=>{
  const record=shrinkRecord(),original=mismatch(record,{stage:'irOptimized'});
  const result=await minimize(record,original,async r=>mismatch(r,{stage:'irOptimized'}),{stage:'irOptimized'});
  assert.equal(result.stage,'irOptimized');assert.equal(result.complete,true);
  await assert.rejects(minimize(record,original,async r=>mismatch(r),{stage:'ir'}),/requires a mismatch/);
  await assert.rejects(minimize(record,original,async r=>mismatch(r),{stage:'wrong'}),/invalid shrink stage/);
});


test('minimization cannot switch compiler optimizer configuration',async()=>{
  const record=shrinkRecord(),original=mismatch(record);
  await assert.rejects(minimize(record,original,async r=>({...mismatch(r),optimizer:false})),/compiler mode changed/);
});

test('reference must execute exactly the generated run selector',async()=>{
  for (const calldata of [undefined,null,'0x1','0x87654321','0x1234567800']) {
    let calls=0;
    const r=await runCase(generate(1)[0],{compile,reference:async()=>({...observation(),calldata}),
      lean:async()=>{calls++;return {status:'ok',observation:observation()};}});
    assert.equal(calls,0);assert.deepEqual(r.results.map(x=>[x.status,x.phase]),[['blocked','reference'],['blocked','reference']]);
  }
});
