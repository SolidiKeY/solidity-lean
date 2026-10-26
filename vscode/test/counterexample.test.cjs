'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const { parseReport } = require('../src/backend.cjs');
const { validateCounterexample, counterexampleDetail } = require('../src/counterexample.cjs');
const model = require('../src/model.cjs');
const { evidence } = require('./witness.cjs');
const row = counterexample => ({ source: '/tmp/C.sol', contract: 'C', function: 'f', status: 'refuted', counterexample });
const parse = value => parseReport(JSON.stringify({ results: [value], errors: [] }));

test('accepts exact typed model evidence and preserves full-width values and signed ledger amounts', () => {
  const witness = evidence({ initialLedger: [{ address: ((1n << 256n) - 1n).toString(), amount: '-' + '9'.repeat(100) }] });
  const report = parse(row(witness));
  assert.deepEqual(report.results[0].counterexample, witness);
  assert.equal(model.resultKind(report.results[0]), 'failed');
  const diagnostic = model.diagnostics(report)[0];
  assert.equal(diagnostic.severity, 'error');
  assert.equal(diagnostic.code, 'refuted');
  assert.match(diagnostic.message, /certified model prestate/);
  assert.ok(diagnostic.message.includes(witness.arguments[0].value));
  assert.ok(diagnostic.message.includes(witness.initialLedger[0].amount));
});
test('requires certified source-goal evidence and audited certificate metadata', () => {
  for (const invalid of [undefined, null, {}, evidence({ kind: 'trace' }), evidence({ certified: false }), evidence({ goalKind: 'cleanTail' }), evidence({ certificateDeclaration: ' ' }), evidence({ axioms: ['sorryAx'] }), evidence({ axioms: 'propext' }), evidence({ lines: [4] })]) {
    assert.throws(() => parse(row(invalid)), /invalid certified model prestate/);
  }
  for (const status of ['pending', 'proved', 'ready', 'error', 'unsupported']) assert.throws(() => parse({ ...row(evidence()), status }), /non-refuted/);
  assert.throws(() => parse({ ...row(null), status: 'pending' }), /non-refuted/);
});
test('rejects lossy, out-of-range, mistyped and noncanonical model arguments', () => {
  const invalid = [
    { modelName: '', type: 'uint', value: '0' }, { modelName: 'p', type: 'uint', value: 1 },
    { modelName: 'p', type: 'uint', value: '-1' }, { modelName: 'p', type: 'uint', value: (1n << 256n).toString() },
    { modelName: 'p', type: 'int', value: (1n << 255n).toString() }, { modelName: 'p', type: 'int', value: (-(1n << 255n) - 1n).toString() },
    { modelName: 'p', type: 'bool', value: 'true' }, { modelName: 'p', type: 'address', value: '0' },
    ...['01', '-0', '+1', '1.0', '0x10', ' 1', '1e5'].map(value => ({ modelName: 'p', type: 'int', value })),
    { modelName: 'p', type: 'uint', value: '0', paramIndex: -1 }
  ];
  for (const argument of invalid) assert.throws(() => validateCounterexample(row(evidence({ arguments: [argument] }))), /invalid certified/);
});
test('validates transaction, ledger, balance and limited outcome data', () => {
  const validTransaction = evidence().transaction;
  for (const overrides of [
    { transaction: null }, { transaction: {} }, { transaction: { ...validTransaction, ext: [{}] } },
    { transaction: { ...validTransaction, msgValue: 0 } }, { transaction: { ...validTransaction, selfAddress: '-1' } },
    { initialLedger: [{}] }, { initialLedger: [{ address: '0', amount: '-0' }] }, { initialLedger: [{ address: '-1', amount: '0' }] },
    { initialBalance: (1n << 256n).toString() }, { initialBalance: 0 }, { initialStorage: {} },
    { outcome: { kind: 'exploit' } }, { outcome: { kind: 'halt', halt: 4 } }, { outcome: [] }
  ]) assert.throws(() => validateCounterexample(row(evidence(overrides))), /invalid certified/);
  validateCounterexample(row(evidence({ outcome: { kind: 'postStorage', storage: 'saved default 0 1' } })));
  const noOutcome = evidence(); delete noOutcome.outcome;
  validateCounterexample(row(noOutcome));
});
test('renders model labels without guessing source parameters and escapes control characters', () => {
  const witness = evidence({ lines: ['[run](command:evil) <img src=x>', '\u001b[31m\nfake-header'], arguments: [{ modelName: 'model0', type: 'uint', value: '5', paramIndex: 0, sourceName: 'source0', sourceType: 'address' }] });
  const detail = counterexampleDetail(row(witness));
  assert.match(detail, /model0 \(uint; source source0: address\) = 5/);
  const noMapping = counterexampleDetail(row(evidence({arguments:[{modelName:'onlyModel',type:'bool',value:false}]})));
  assert.match(noMapping, /onlyModel \(bool\) = false/);
  assert.doesNotMatch(noMapping, /source /);
  assert.match(detail, /\\u001b\[31m\\u000afake-header/);
  assert.doesNotMatch(detail, /constructor-reachable|execution trace|exploit/i);
});

test('does not present unvalidated transport fields as certificate observations', () => {
  const witness = evidence();
  witness.transaction.futureClaim = { arbitrary: 'not validated' };
  witness.outcome.futureClaim = 'not validated';
  witness.initialLedger = [{ address:'0', amount:'1', futureClaim:'not validated' }];
  validateCounterexample(row(witness));
  assert.doesNotMatch(counterexampleDetail(row(witness)), /futureClaim|not validated/);
});
