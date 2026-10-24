import { test } from 'node:test';
import assert from 'node:assert/strict';
import { audit, findings } from './check-trust.mjs';

test('comments and strings cannot manufacture or hide proof escapes', () => {
  assert.deepEqual(findings('/- sorry /- axiom -/ native_decide -/\n-- admit\n#eval r#"sorry \\""#'), []);
  for (const code of ['by sorry', 'by admit', 'by native_decide', 'by decide +native', 'axiom bad : False', 'exact sorryAx _ true'])
    assert.ok(findings(code).some(x => x.kind === 'forbidden'), code);
  assert.ok(findings('"/-"\naxiom bad : False').some(x => x.kind === 'forbidden'));
  assert.ok(findings('by decide\n  +native').some(x => x.kind === 'forbidden'));
  assert.ok(findings('s!"{(by sorry : Nat)}"').some(x => x.kind === 'forbidden'));
  assert.ok(findings('m!"{s!"{(by sorry : Nat)}"}"').some(x => x.kind === 'forbidden'));
  assert.ok(findings('def s := r#"a" /- "#\naxiom bad : False').some(x => x.kind === 'forbidden'));
  assert.equal(findings('opaque\nα : Nat')[0]?.kind, 'opaque');
  assert.deepEqual(findings('def s := r###"sorry " /- axiom"###'), []);
  for (const id of ['«/-»', '«x"»', '«--»', '«x}»'])
    assert.ok(findings(`def ${id} := 1\naxiom bad : False`).some(x => x.kind === 'forbidden'));
  assert.ok(findings('exact Lean.«ofReduceBool» x').some(x => x.kind === 'forbidden'));
  for (const prefix of ['s! ', 's!\n ', 'm! /- formatting -/ ', 'dbg_trace ', 'throwErrorAt stx '])
    assert.ok(findings(prefix + '"{(by sorry : Nat)}"').some(x => x.kind === 'forbidden'), prefix);
  assert.ok(findings('def s := "{"\naxiom bad : False').some(x => x.kind === 'forbidden'));
  // Ordinary brace text is deliberately conservative; raw snippets are literal.
  assert.ok(findings('def s := "{sorry}"').some(x => x.kind === 'forbidden'));
  assert.deepEqual(findings('def s := r#"{sorry}"#'), []);
  assert.ok(findings('s!"{(let q := "{"; (by sorry : Nat))}"').some(x => x.kind === 'forbidden'));
  assert.ok(findings('"/- sorry -/"').some(x => x.kind === 'forbidden'));
});

test('implementation and recovery sites require exact counted inventory', () => {
  const files = [['X.lean', '@[implemented_by fast]\ndef f := 1\n g.admit']];
  const result = audit(files, []);
  assert.equal(result.errors.length, 2);
  assert.deepEqual(audit(files, result.actual).errors, []);
  assert.ok(audit([['X.lean', files[0][1] + '\n g.admit']], result.actual).errors.length);
  assert.ok(audit([['X.lean', files[0][1].replace('fast', 'other')]], result.actual).errors.length);
  assert.ok(audit([], result.actual).errors.length);
});
