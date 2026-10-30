import test from 'node:test';
import assert from 'node:assert/strict';
import {cumulativeTiming,replayModules} from './check-memory-loop-timing.mjs';
const good=()=>({kind:'fresh-original-Derived17-workload',exit_code:0,budgetSeconds:300,seconds:240,checks:replayModules.map(module=>({module,fresh:true,exit_code:0,seconds:9,sourceSha256:'0'.repeat(64)}))});
test('complete original workload with current sources passes',()=>assert.deepEqual(cumulativeTiming(good(),()=> '0'.repeat(64)),[]));
test('per-stage allowances do not evade cumulative300',()=>{const r=good();r.seconds=965.51;r.checks.forEach(c=>c.seconds=40);assert.ok(cumulativeTiming(r).length);});
test('cached, partial, duplicate, stale, failed and raised-budget evidence refused',()=>{
  for(const change of [r=>r.checks.pop(),r=>r.checks[0].fresh=false,r=>r.checks[0].module=r.checks[1].module,r=>r.exit_code=75,r=>r.budgetSeconds=1000,r=>r.seconds='240',r=>r.seconds=[240],r=>r.checks[0].fresh='cached',r=>r.checks[0].exit_code=1,r=>r.checks[0].seconds=299,r=>r.checks[0].sourceSha256='bad',r=>r.checks=null]) {const r=good();change(r);assert.ok(cumulativeTiming(r).length);}
  assert.ok(cumulativeTiming(good(),()=> '1'.repeat(64)).length);
});
