import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { check } from './check-v11-disjoint-schedules.mjs';
const registry = JSON.parse(readFileSync('tests/v11-disjoint-schedules-statements.json', 'utf8'));
const clean = Object.fromEntries(Object.keys(registry.files).map(f => [f, readFileSync(f, 'utf8')]));
const core = 'Solidity/Backend/MemoryOps/DisjointSnapshotSchedules.lean';
const controls = 'Solidity/Backend/MemoryOps/DisjointSnapshotScheduleControls.lean';
const app = 'Solidity/Backend/MemoryOps/DisjointSnapshotPathApplications.lean';
function reject(file, change) {
  const text = change(clean[file]); assert.notEqual(text, clean[file]);
  assert.ok(check({...clean, [file]:text}, registry).length > 0);
}
test('original checked statements and standard guards pass', () => assert.deepEqual(check(clean, registry), []));
test('dropped logical separation is rejected', () => reject(core, s => s.replace('(hne : r.id≠q.id)', '(hne : True)')));
test('a false premise cannot make coverage vacuous', () => reject(app, s => s.replace('theorem fixed_shared_paths (n : Nat)', 'theorem fixed_shared_paths (n : Nat) (impossible : False)')));
test('changed ordered primitive vector is rejected', () => reject(controls, s => s.replace('[[true,false,false],[false,true,true]', '[[false,false,false],[false,true,true]')));
test('empty-object observation cannot disappear', () => reject(app, s => s.replace('MObj.elems .fixed (hp.get fixedEmpty)=[]', 'True')));
test('a missing exact axiom guard is rejected', () => reject(core, s => s.replace('#guard_msgs (whitespace := lax) in #print axioms runCaptures_disjoint_comm', '#check runCaptures_disjoint_comm')));
test('nonstandard axiom pin is rejected', () => reject(core, s => s.replace('[propext, Quot.sound]', '[propext, sorryAx]')));
test('native proof shortcut is rejected', () => reject(core, s => s + '\nexample : True := by native_decide\n'));
test('a new axiom is rejected', () => reject(core, s => s + '\naxiom bypass : False\n'));
test('erasing explicit typed-path client calls is rejected', () => reject(app, s => s.replaceAll(':= runCaptures_disjoint_path', ':= rfl')));

test('duplicate permitted guard cannot hide a missing headline', () => reject(core, s => {
  function block(name) {
    const lines = s.split('\n');
    const at = lines.findIndex(l => l.includes('#print axioms ' + name) && l.trimEnd().endsWith(name));
    assert.ok(at > 0); return lines.slice(at - 1, at + 1).join('\n');
  }
  return s.replace(block('runCaptures_disjoint_comm'), block('runCaptures_disjoint_success'));
}));
test('standard but unobserved axiom set is rejected', () => reject(core, s => s.replace('[propext, Quot.sound]', '[propext, Classical.choice, Quot.sound]')));
test('wrong printed theorem name is rejected', () => reject(core, s => s.replace("'Solidity.Backend.MemoryOps.runCaptures_disjoint_comm'", "'Solidity.Wrong.runCaptures_disjoint_comm'")));
