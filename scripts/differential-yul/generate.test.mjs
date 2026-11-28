import {test} from 'node:test';
import assert from 'node:assert/strict';
import {generate, sourceFor, reductions, families} from './generate.mjs';
test('2000 reproducible distinct sources span every family and full-width operands', () => {
  const records = generate();
  assert.deepEqual(records, generate());
  assert.equal(new Set(records.map(r => r.source)).size, 2000);
  assert.deepEqual(new Set(records.map(r => r.family)), new Set(families));
  assert.ok(records.some(r => BigInt(r.a) === (1n << 256n) - 1n));
  assert.notDeepEqual(records, generate(2000, 1129));
  for (const family of families) for (const operand of ['a','b']) {
    const values = records.filter(r => r.family === family).map(r => r[operand]);
    assert.ok(new Set(values).size > 100, `${family}.${operand} lacks random coverage`);
    assert.ok(values.some(v => BigInt(v) > (1n << 255n) && BigInt(v) < (1n << 256n)-1n));
  }
});
test('generator rejects malformed inputs and never emits expected observations', () => {
  for (const count of [0, -1, 10001, NaN, 1.5]) assert.throws(() => generate(count));
  for (const seed of [-1, 2**32, NaN]) assert.throws(() => generate(1, seed));
  const [r] = generate(1);
  for (const a of ['-1','01','0; revert()',String(1n<<256n)]) assert.throws(() => sourceFor({...r,a}));
  assert.equal('expected' in r, false);
});
test('reduction candidates strictly decrease an operand and regenerate source', () => {
  const r = {...generate(1)[0], a:'19', b:'8', rounds:7};
  for (const c of reductions(r)) {
    assert.ok(BigInt(c.a) + BigInt(c.b) + BigInt(c.rounds) < 34n);
    assert.equal(c.source, sourceFor(c));
    assert.equal(c.family, r.family);
  }
});
