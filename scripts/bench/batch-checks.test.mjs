// Guard against missing batch checkpoints, wrong identities and false native successes.
import test from 'node:test';
import assert from 'node:assert/strict';
import {observations, runAdmissionChecks} from './batch-checks.mjs';
const row = {source:'/a.sol',sourceHash:'h',contract:'C',sourceId:1,signature:'f()',status:'ready'};
test('a partial batch retains every unobserved and refused inventory row',()=>{
 const other={...row,sourceId:2,status:'unsupported'};
 const result=observations([row,other],{results:[]});
 assert.equal(result.rows.length,2);assert.equal(result.missingReadyRows,1);
 assert.equal(result.rows[0].functionReportedElapsedMs,null);
 assert.equal(result.rows[1].certifiedCheckPassed,false);
});
test('native, ambiguous and wrong declaration results cannot become certified checks',()=>{
 for (const results of [[{...row,status:'proved',verification:'direct'}],
   [{...row,status:'proved'},{...row,status:'proved'}],
   [{...row,sourceHash:'other',status:'proved'}]]) {
  const result=observations([row],{results});assert.equal(result.rows[0].certifiedCheckPassed,false);
 }
});
test('reported check time stays distinct from source-to-verdict and RSS',()=>{
 const result=observations([row],{results:[{...row,status:'proved',elapsedMs:12}]});
 assert.equal(result.rows[0].certifiedCheckPassed,true);
 assert.equal(result.rows[0].functionReportedElapsedMs,12);
 assert.equal(result.rows[0].sourceToVerdictWallMs,null);
 assert.equal(result.rows[0].maxRss,null);
});

test('identical bytes at different source paths do not share observations',()=>{
 const other={...row,source:'/b.sol'};
 const result=observations([row,other],{results:[{...row,status:'proved'}]});
 assert.equal(result.rows[0].certifiedCheckPassed,true);
 assert.equal(result.rows[1].certifiedCheckPassed,false);
 assert.equal(result.missingReadyRows,1);
});
test('duplicate inventory identities cannot double-credit a single check',()=>{
 const result=observations([row,row],{results:[{...row,status:'proved'}]});
 assert.equal(result.duplicateInventoryKeys.length,1);
 assert.equal(result.ambiguousRows,2);
 assert.ok(result.rows.every(r=>!r.certifiedCheckPassed));
});

test('unattempted and unknown statuses keep raw placeholders but expose no check timer',()=>{
 for(const status of ['notRun','ready','internal','unsupported','excluded','elaborated','skip','skipped','future',undefined]) {
  const result=observations([row],{results:[{...row,status,elapsedMs:0}]});
  assert.equal(result.rows[0].functionReportedElapsedMs,null,status);
  assert.equal(result.rows[0].observations[0].elapsedMs,0);
 }
 for(const verification of ['direct','native']) {
  const result=observations([row],{results:[{...row,status:'proved',verification,elapsedMs:0}]});
  assert.equal(result.rows[0].functionReportedElapsedMs,null);
 }
});
test('attempted zero is real while invalid Nat timers and ambiguous identities remain unavailable',()=>{
 for(const status of ['proved','refuted','pending','error']) {
  const result=observations([row],{results:[{...row,status,elapsedMs:0}]});
  assert.equal(result.rows[0].functionReportedElapsedMs,0);
 }
 for(const elapsedMs of [-1,0.5,NaN,Infinity,Number.MAX_SAFE_INTEGER+1,'0',null,undefined]) {
  const result=observations([row],{results:[{...row,status:'proved',elapsedMs}]});
  assert.equal(result.rows[0].functionReportedElapsedMs,null);
  assert.equal(result.rows[0].certifiedCheckPassed,true);
 }
 for(const [inventory,results] of [[[row,row],[{...row,status:'proved',elapsedMs:2}]],[[row],[{...row,status:'proved',elapsedMs:2},{...row,status:'proved',elapsedMs:2}]]]) {
  assert.ok(observations(inventory,{results}).rows.every(r=>r.functionReportedElapsedMs===null));
 }
});

// Guard landing review F2: a selected inventory must not launch unrelated proofs.
test('actual batch API call preserves exact admission selectors and smaller tool timeout',()=>{
 const admission={inputs:[{path:'/a.sol'}],selection:{contract:'Only',function:'f(uint256)',timeoutMs:1234}};
 let calls=0;
 const result=runAdmissionChecks(admission,{soljson:'/compiler'},(paths,options)=>{
  calls++;assert.deepEqual(paths,['/a.sol']);
  assert.equal(options.contract,'Only');assert.equal(options.function,'f(uint256)');
  assert.equal(options.timeoutMs,1234);assert.equal(options.build,false);assert.equal(options.batchSize,32);
  return {results:[{contract:options.contract,signature:options.function}],errors:[]};
 });
 assert.equal(calls,1);assert.deepEqual(result.results,[{contract:'Only',signature:'f(uint256)'}]);
});
test('unselected snapshots remain unselected, timeouts stay capped and malformed selectors launch nothing',()=>{
 for(const selection of [undefined,{}, {timeoutMs:400000}]) {
  runAdmissionChecks({inputs:[],selection},{},(_paths,options)=>{
   assert.equal(options.contract,undefined);assert.equal(options.function,undefined);
   assert.equal(options.timeoutMs,300000);return {results:[],errors:[]};
  });
 }
 for(const selection of [{contract:3},{function:''},{timeoutMs:0},{timeoutMs:1.5}]) {
  assert.throws(()=>runAdmissionChecks({inputs:[],selection},{},()=>assert.fail('invalid selection launched checks')));
 }
});
