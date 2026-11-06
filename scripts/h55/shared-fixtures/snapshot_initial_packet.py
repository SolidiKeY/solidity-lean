#!/usr/bin/env python3
"""Emit an unapplied exact-base proposal for three identical initial fixtures."""
import difflib
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'
AREA = 'Solidity/Backend/StorageOps/'
FILES = [AREA + 'PrimitiveSnapshot' + n + 'Controls.lean' for n in ('Dependent', 'Repeat', 'Sequence')]
HELPER = AREA + 'SharedSnapshotInitialFixture.lean'
OLD = 'private def initial : WordStore := fun a => if a<16 then captured (.root a) else captured (part (a-16))'
NEW = 'private def initial : WordStore := SharedSnapshotInitialFixture.initial captured part'
CONTENT = '''import Solidity.Storage.Representation.Transport

/-! Proposed shared snapshot initial-store fixture. -/
namespace Solidity.Backend.StorageOps.SharedSnapshotInitialFixture
open Solidity.Storage Solidity.Storage.Representation

def initial (captured : Store) (part : Nat → Loc) : WordStore :=
  fun a => if a<16 then captured (.root a) else captured (part (a-16))

end Solidity.Backend.StorageOps.SharedSnapshotInitialFixture
'''


def emit(old, new, a, b):
    sys.stdout.writelines(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile=a, tofile=b))


if (ROOT / HELPER).exists():
    raise SystemExit('proposed helper already exists')
for path in FILES:
    old = subprocess.check_output(['git', 'show', f'{BASE}:{path}'], cwd=ROOT, text=True)
    if old.count(OLD) != 1 or (ROOT / path).read_text() != old:
        raise SystemExit(f'baseline precondition failed: {path}')
    new = 'import Solidity.Backend.StorageOps.SharedSnapshotInitialFixture\n' + old.replace(OLD, NEW)
    emit(old, new, 'a/' + path, 'b/' + path)
emit('', CONTENT, '/dev/null', 'b/' + HELPER)
