import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {runSolidityTests} from './test-solidity.mjs';
import {solkeyTestOptions} from './test-compiler.mjs';

const source = 'tests/solc/EntryPointsLeft.sol';
const compilerOptions = solkeyTestOptions();
const sha = bytes => createHash('sha256').update(bytes).digest('hex');
test('entry fixtures retain the same source and exact compiler/settings in both pipelines', () => {
  for (const [suffix, viaIR] of [['ast.json',false], ['viaIR.ast.json',true]]) {
    const fixture = JSON.parse(readFileSync(`tests/solc/EntryPointsLeft.${suffix}`));
    assert.equal(fixture.header.sourceSha256, sha(readFileSync(source)));
    assert.equal(fixture.header.compilerSha256, '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390');
    assert.equal(fixture.header.settings.viaIR, viaIR);
  }
});

const cases = [
  ['ContractKeyGetter', {positive:'proved'}],
  ['NominalGetters', {enumScalar:'proved', enumMapping:'proved', enumStruct:'proved', contractScalar:'proved', falseEnum:'pending'}],
  ['InheritedReceiver', {positive:'proved', falseObservation:'pending', stipendRefusal:'unsupported'}],
  ['InheritedFallback', {positive:'proved', falseObservation:'pending'}],
  ['RenamedExternal', {positive:'proved', falseObservation:'pending'}],
  ...['ReceivePriority','ReceiveOverride','ExternalOverride','ExternalOverloads','OwnHelperReceiver',
    'InheritedFrameReceiver','InheritedFrameFallback','InheritedRollback'].map(name => [name,{positive:'proved'}]),
  ...['NonpayableFallbackRefusal','ModifiedReceiverRefusal','HelperReceiverRefusal','ByteFallbackRefusal',
    'NominalDispatchRefusal','NominalKeyDispatchRefusal'].map(name => [name,{entry:'unsupported'}]),
  ['ExternalOverloadCollisionRefusal', {positive:'unsupported'}],
  ['RefusedGetters', {referenceBytes:'unsupported', referenceString:'unsupported', functionResult:'unsupported'}],
];
for (const [contract, expected] of cases) test(`entry source verdicts: ${contract}`, () => {
  const report = runSolidityTests([source], {...compilerOptions, build:false, contract, batchSize:1});
  if (process.env.SOLIDITY_ENTRY_EVIDENCE_DIR) {
    mkdirSync(process.env.SOLIDITY_ENTRY_EVIDENCE_DIR, {recursive:true});
    writeFileSync(`${process.env.SOLIDITY_ENTRY_EVIDENCE_DIR}/${contract}.json`, JSON.stringify(report,null,2)+'\n');
  }
  assert.deepEqual(report.errors, []);
  for (const [name,status] of Object.entries(expected)) {
    const row = report.results.find(row => row.function === name);
    assert.equal(row?.status, status, JSON.stringify(row));
    if (status === 'unsupported' && !['referenceBytes','referenceString'].includes(name)) {
      const code = ['InheritedReceiver','NonpayableFallbackRefusal','ModifiedReceiverRefusal','HelperReceiverRefusal','ByteFallbackRefusal'].includes(contract)
        ? 'solidity.selfPayment' : 'solidity.functionDispatch';
      assert.ok(row.reason?.includes(code), JSON.stringify(row));
    }
  }
});
