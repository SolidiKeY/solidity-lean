import {test} from 'node:test';
import assert from 'node:assert/strict';
import {runSolidityTests,testsPassed} from './test-solidity.mjs';
import backend from '../vscode/src/backend.cjs';

const source = 'tests/solc/Counterexamples.sol';

test('source counterexamples are opt-in and cannot be requested during listing', () => {
  assert.throws(() => runSolidityTests([source],{build:false,list:true,counterexamples:true}), /omit --list/);
  const plain = runSolidityTests([source],{build:false,function:'falsePost(uint)'});
  assert.deepEqual(plain.errors,[]);
  assert.equal(plain.results[0].status,'pending');
  assert.equal(plain.results[0].counterexample,undefined);
});

test('certified source counterexamples preserve exact overloads, model values and source names', () => {
  const report = runSolidityTests([source],{build:false,counterexamples:true,batchSize:3});
  assert.deepEqual(report.errors,[]);
  const row = signature => {
    const found = report.results.find(r => r.signature === signature);
    assert.ok(found,signature);
    return found;
  };
  for (const signature of ['falsePost(uint)','falsePost(bool)','large(uint)','names(address,uint,uint,int,bool)']) {
    const found = row(signature);
    assert.equal(found.status,'refuted',`${signature}: ${found.reason}`);
    const c = found.counterexample;
    assert.equal(c.kind,'model-state');
    assert.equal(c.certified,true);
    assert.equal(c.goalKind,'fmlValid');
    assert.match(c.certificateDeclaration,/refuted$/);
    assert.ok(c.axioms.every(a => ['propext','Classical.choice','Quot.sound'].includes(a)));
    assert.ok(c.lines.length > 0);
    assert.ok(found.range && found.sourceHash);
  }
  assert.equal(row('falsePost(uint)').counterexample.arguments[0].value,'2');
  assert.equal(typeof row('falsePost(bool)').counterexample.arguments[0].value,'boolean');
  assert.equal(row('large(uint)').counterexample.arguments[0].value,(2n**256n-1n).toString());
  const names = row('names(address,uint,uint,int,bool)').counterexample.arguments;
  assert.deepEqual(names.map(a => a.sourceName),['from','value','value_','$x','']);
  assert.deepEqual(names.map(a => a.sourceType),['address','uint256','uint256','int256','bool']);
  assert.equal(new Set(names.map(a => a.modelName)).size,5);
  for (const signature of ['correct(uint)','vacuous(uint)']) {
    assert.equal(row(signature).status,'proved');
    assert.equal(row(signature).counterexample,undefined);
  }
  for (const signature of ['plain()','recursive(uint)']) {
    assert.equal(row(signature).status,'pending');
    assert.equal(row(signature).counterexample,undefined);
  }
  assert.equal(testsPassed(report),false);
  assert.doesNotThrow(() => backend.parseReport(JSON.stringify(report)));
});

test('callback obligations retain their reading and stay pending without model evidence', () => {
  const report = runSolidityTests(['tests/solc/AuditCallbacks.sol'],{
    build:false,counterexamples:true,function:'specified',
  });
  assert.deepEqual(report.errors,[]);
  assert.equal(report.results[0].status,'pending');
  assert.equal(report.results[0].counterexample,undefined);
});
