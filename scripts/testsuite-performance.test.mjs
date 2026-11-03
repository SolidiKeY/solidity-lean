import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {suiteSources} from './testsuite-performance.mjs';

test('each of the 83 linked Velvet functions has an isolated, matching workload',()=>{
  const text=fs.readFileSync(new URL('../Bridge/SolidityVelvet/TestSuite.lean',import.meta.url),'utf8');
  const rows=suiteSources(text);
  assert.equal(rows.length,83);
  assert.deepEqual(rows.map(r=>r.name),[...text.matchAll(/^  function (\w+)\(/gm)].map(m=>m[1]));
  for(const row of rows){
    assert.equal([...row.source.matchAll(/\bfunction (\w+)\(/g)].length,1);
    assert.ok(row.source.includes('function '+row.name+'('));
    assert.ok(row.source.includes('/// @custom:key box'));
    assert.ok(!row.source.includes('−−'));
    assert.ok(!/^\s*invariant /m.test(row.source));
  }
  const loop=rows.find(r=>r.name==='forWritesStorageArray').source;
  assert.match(loop,/\/\/\/ @custom:key invariant \\forall uint j; j < i -> values\[j\] == j \* j/);
  assert.ok(loop.indexOf('/// @custom:key invariant')<loop.indexOf('for ('));
  assert.ok(rows.find(r=>r.name==='storageRootPredecrement').source.includes('--age;'));
});

test('an incomplete function body cannot silently reduce the benchmark inventory',()=>{
  assert.throws(()=>suiteSources('contract TestSuite {\n  function f() public {'),/Unterminated/);
});
