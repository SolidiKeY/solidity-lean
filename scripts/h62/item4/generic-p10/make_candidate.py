#!/usr/bin/env python3
"""Reproduce an additive BYTE-control migration overlay, never edit the owner.

This is the finite P10 BYTE family, not the H55 Yul/vector generator. Every
original declaration signature and negative/refusal proof is retained. New
statements still require Lean checking; generation is not a proof.
"""
import argparse
from pathlib import Path
import re
import subprocess
import census

SOURCE = Path('Bridge/SolidityBridge/RoadmapV15/P10/ByteObservationControls.lean')
OUTPUT = Path('tests/h62/item4/generic-p10/GenericP10/ByteControls.lean')
CASES = {
    'first_byte': 'first', 'second_byte': 'second', 'middle_zero': 'middle',
    'penultimate_byte': 'penultimate', 'last_byte': 'last', 'outside_word': 'outside',
    'maximum_index': 'maximumIndex', 'zero_word': 'zero', 'maximum_word': 'maximumWord',
}
OBSERVED_PROOF = ''' by
  have h : Assembly.driverSteps 1 2 #[] (input index value) =
      .ok {input index value with
        gasAvailable := u 9-u 3,pc := u 3+u 1,execLength := 42
        stack := [u result,u 258,u 513]} :=
    (GenericP10.execute (site 9) (BitVec.ofNat 256 index)
      (BitVec.ofNat 256 value) (BitVec.ofNat 256 result) word [258,513]
      (by decide +kernel) (by decide +kernel) 0).1
  rw [show u 9-u 3=u 6 from by decide +kernel,
    show u 3+u 1=u 4 from by decide +kernel] at h
  exact h
'''
TABLE_CASE = '''
private theorem table_case (c : GenericP10.ByteCase) :
    Assembly.driverSteps 1 2 #[]
      (input (GenericP10.fixture c).index.val (GenericP10.fixture c).value.val) =
    .ok (expected (GenericP10.fixture c).index.val (GenericP10.fixture c).value.val
      (GenericP10.fixture c).result.val) :=
  observed _ _ _ (GenericP10.fixture c).word_eq

'''


def candidate(original):
    result = original.replace('import SolidityBridge.RoadmapV15.P10.ByteObservation\n',
                              'import GenericP10.ByteFixture\n', 1)
    result = result.replace('SolidityBridge.RoadmapV15.P10.ByteObservationControls', 'GenericP10.ByteControls')
    result = result.replace('namespace GenericP10.ByteControls\n',
        'namespace GenericP10.ByteControls\nopen SolidityBridge.RoadmapV15.P10\n', 1)
    start = result.index('private theorem observed')
    proof = result.index(' := by\n', start)
    end = result.index('\nprivate def payload', proof)
    result = result[:proof+3]+OBSERVED_PROOF+result[end:]
    for name, label in CASES.items():
        pattern = r'(theorem '+re.escape(name)+r'\s*:[\s\S]*?:= by\n)  apply observed\n  decide \+kernel\n'
        result, count = re.subn(pattern, lambda m: m.group(1)+f'  exact table_case .{label}\n', result, count=1)
        if count != 1: raise ValueError(f'original control shape changed: {name}')
    result = result.replace('\ntheorem first_byte', '\n'+TABLE_CASE+'theorem first_byte', 1)
    old = {r['name']: r for r in census.declarations(original, SOURCE.as_posix())}
    new = {r['name']: r for r in census.declarations(result, OUTPUT.as_posix())}
    for name, row in old.items():
        if name not in new or row['statement_sha256'] != new[name]['statement_sha256']:
            raise ValueError(f'original statement changed or omitted: {name}')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    original = (args.repo/SOURCE).read_bytes()
    frozen = subprocess.check_output(['git', '-C', str(args.repo), 'show', f'{census.BASE}:{SOURCE.as_posix()}'])
    if original != frozen: raise SystemExit('owner source differs from frozen base; stop for relay')
    result = candidate(original.decode())
    output = args.repo/OUTPUT
    if args.check:
        if output.read_text() != result: raise SystemExit('additive candidate is not reproducible')
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(result)
    print('CANDIDATE_SOURCE_PASS: exact original signatures retained; nine table applications; Lean proof gate separate')


if __name__ == '__main__': main()
