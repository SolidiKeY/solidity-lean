import test from 'node:test';
import assert from 'node:assert/strict';
import {classify, timings, proofs} from './check-automatic.mjs';
test('checked replay retains the original explicit 1024 budget', () => {
  assert.deepEqual(classify(['finish_memory_replay']), {kind:'budget', steps:1024});
  for (const body of [['finish_memory_replay','sol_close'], ['finish_memory_replay (steps := 2048)'], ['first | finish_memory_replay | omega']])
    assert.equal(classify(body).kind, 'manual');
});
test('stage timing includes nested modules and unchanged time threshold inputs', () => {
  assert.deepEqual(timings('✔ [1/2] Built Solidity.TestSuite.MemoryLoopReplay.Discover00 (2m 3s)'), [['Solidity.TestSuite.MemoryLoopReplay.Discover00',123]]);
});
test('moved theorem remains visible to command parsing', () => {
  const ps=proofs('theorem Solkey.TestSuite.returnLeavesNestedLoops.proved :\n    ⊢ Solkey.TestSuite.returnLeavesNestedLoops.problem := by\n  finish_memory_replay\n');
  assert.equal(ps.length,1); assert.deepEqual(ps[0].body,['finish_memory_replay']);
});
