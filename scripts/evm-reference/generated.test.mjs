import test from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync, spawnSync} from 'node:child_process';
import {resolve} from 'node:path';
import {compiler, execute, compare, variants, shrink} from './generated.mjs';
const binary = resolve('.lake/build/bin/solcases');
const generate = seed => execFileSync(binary,[String(seed)],{encoding:'utf8'}).trim().split('\n').map(JSON.parse);
const records = generate(0);
const compile = compiler(process.env.SOLC_REFERENCE ?? '/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js');

test('enumeration is reproducible, typed and includes boundary states and rollback',()=>{
  assert.equal(records.length,160);
  assert.deepEqual(records,generate(0));
  assert.equal(new Set(records.map(r=>r.source)).size,160);
  assert.deepEqual(new Set(records.map(r=>r.kind)),new Set(Array.from({length:10},(_,i)=>i)));
  assert.deepEqual(new Set(generate(1).map(r=>r.source)),new Set(records.map(r=>r.source)));
  assert.ok(records.some(r=>r.expected.revertData.startsWith('0x4e487b71')));
  assert.ok(records.some(r=>r.kind===7 && r.expected.failed));
  for (const args of [['bad'],['1','extra']]) assert.notEqual(spawnSync(binary,args).status,0);
});

for (const variant of variants) test(`generated rollback/panic/branch controls ${JSON.stringify(variant)}`,async()=>{
  for (const index of [0,3,6,7,8,9,30,38,159]) {
    const record = records[index];
    const actual = await execute(record,variant,compile);
    assert.equal(actual.status,'agree',JSON.stringify(actual));
    const wrongStorage = structuredClone(actual);
    wrongStorage.rawStorage[0] = '999';
    assert.equal(compare(record,wrongStorage),false,'raw storage mutation must fail');
    const wrongReturn = structuredClone(actual);
    wrongReturn.run.returnData = '0xdeadbeef';
    assert.equal(compare(record,wrongReturn),false,'wrong revert/output bytes must fail');
    const wrongGetter = structuredClone(actual);
    wrongGetter.storage.returnData = '0x';
    assert.equal(compare(record,wrongGetter),false,'getter mutation must fail');
  }
});

test('unknown layout is blocked and cannot become agreement',async()=>{
  const r = {...records[0],source:records[0].source.replace('uint256 x;','uint256 z; uint256 x;')};
  const result = await execute(r,variants[0],compile);
  assert.equal(result.status,'blocked');
  assert.match(result.reason,/layout/);
});

test('shrinking reexecutes generated operands and records a reproducible mismatch',async()=>{
  const wrong = records.map(r=>r.kind===0 ? {...r,expected:{...r.expected,storage:['x = 999','y = 0']}} : r);
  const result = await shrink(wrong[30],variants[0],wrong,compile);
  assert.ok(result.attempts.length);
  assert.equal(result.actual.status,'mismatch');
  assert.equal(result.record.index,0);
});
