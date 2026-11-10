// Guard against missing batch checkpoints, wrong identities and false native successes.
import test from 'node:test';
import assert from 'node:assert/strict';
import {observations} from './batch-checks.mjs';
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
