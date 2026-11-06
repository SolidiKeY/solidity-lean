#!/usr/bin/env python3
"""Emit an unapproved exact-base proposal for identical private uint syntax fixtures."""
import difflib
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
BASE = '4d3790eadb8a5212233bc7d5e345817476b2f590'
AREA = 'Solidity/Lowering/StorageOps'
HELPER = AREA + '/SharedUintSyntaxFixture.lean'
ORIGINAL = 'private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))'
REPLACEMENT = ('private def uintSyntax : Source.Syn .typeName := '
               'Solidity.Lowering.StorageOps.SharedUintSyntaxFixture.uintSyntax')
CONTENT = '''import Solidity.Source.Syntax

/-! Shared uint syntax fixture proposed for Source storage controls. -/
namespace Solidity.Lowering.StorageOps.SharedUintSyntaxFixture

def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))

end Solidity.Lowering.StorageOps.SharedUintSyntaxFixture
'''


def diff(old, new, a, b):
    sys.stdout.writelines(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile=a, tofile=b))


if (ROOT / HELPER).exists():
    raise SystemExit('proposed helper exists; reassess ownership and scope')
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE, '--', AREA], cwd=ROOT, text=True).splitlines()
proposals = []
for path in sorted(p for p in paths if p.endswith('.lean')):
    old = subprocess.check_output(['git', 'show', f'{BASE}:{path}'], cwd=ROOT, text=True)
    if ORIGINAL not in old:
        continue
    if old.count(ORIGINAL) != 1 or (ROOT / path).read_text() != old:
        raise SystemExit(f'baseline precondition failed: {path}')
    new = 'import Solidity.Lowering.StorageOps.SharedUintSyntaxFixture\n' + old.replace(ORIGINAL, REPLACEMENT)
    proposals.append((path, old, new))
if len(proposals) != 22:
    raise SystemExit(f'expected 22 exact-text candidates, found {len(proposals)}')
for path, old, new in proposals:
    diff(old, new, f'a/{path}', f'b/{path}')
diff('', CONTENT, '/dev/null', f'b/{HELPER}')
