import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = dirname(dirname(fileURLToPath(import.meta.url)));
test('KeY proof mappings connect custom and legacy evidence to the corpus build', { timeout: 120000 }, () => {
  const out = mkdtempSync(join(tmpdir(), 'payment-corpus-'));
  try {
    execFileSync(process.execPath, ['scripts/solkey-port.mjs', '--out', out], {
      cwd: root, timeout: 120000,
      env: { ...process.env, SOLKEY_EXAMPLES: join(root, 'tests/migration/solkey/keyext.solidity.examples') },
    });
    const rows = readFileSync(join(out, 'tests/solkey/expected.tsv'), 'utf8')
      .trim().split('\n').map(line => line.split('\t'));
    const corpus = readFileSync(join(out, 'SolidityCorpus.lean'), 'utf8');
    const oldRows = readFileSync(join(root, 'tests/solkey/expected.tsv'), 'utf8')
      .trim().split('\n').map(line => line.split('\t'));
    const otherRows = rows => rows.filter(row => !(row[0] === 'net' &&
      row[2] === 'piggybank_breakPiggyBank_withcallback'));
    assert.deepEqual(otherRows(rows), otherRows(oldRows));
    const piggy = rows.find(row => row[0] === 'net' && row[2] === 'piggybank_breakPiggyBank_withcallback');
    assert.equal(piggy[3], 'proved');
    assert.match(piggy[5], /Examples\/Tactics\/PaymentCorpus\.lean/);
    assert.match(corpus, /^import Solidity\.Examples\.Tactics\.PaymentCorpus$/m);
    assert.match(corpus, /^#check Solidity\.Examples\.Tactics\.PaymentCorpus\.breakPiggyBank_callback$/m);
    const legacy = rows.find(row => row[0] === 'net' && row[2] === 'net_transfer_simple');
    assert.equal(legacy[3], 'proved');
    assert.match(legacy[5], /Examples\/Tactics\/Net\.lean/);
    assert.equal(corpus.match(/^import Solidity\.Examples\.Tactics\.Net$/gm)?.length, 1);
    assert.match(corpus, /^#check Solidity\.Examples\.Tactics\.Net\.netTransferSimple$/m);
    for (const name of ['net_transfer_withcallback_diamond', 'net_transfer_withcallback_self',
      'net_transfer_withcallback_simple', 'net_call_withcallback_simple', 'casino_decideBet_withcallback', 'auction_makeBid_withcallback']) {
      assert.equal(rows.find(row => row[0] === 'net' && row[2] === name)?.[3], 'unsupported', name);
    }
  } finally {
    rmSync(out, { recursive: true, force: true });
  }
});
