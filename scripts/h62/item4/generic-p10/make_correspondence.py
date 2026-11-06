#!/usr/bin/env python3
"""Generate kernel statement-equality checks for every original public control."""
import argparse
from pathlib import Path
import subprocess
import census
from make_candidate import SOURCE

OUTPUT = Path('tests/h62/item4/generic-p10/GenericP10/Correspondence.lean')


def render(original):
    names = [r['name'] for r in census.declarations(original, SOURCE.as_posix())
             if r['kind'] == 'theorem' and not r['private']]
    text = '''import SolidityBridge.RoadmapV15.P10.ByteObservationControls
import GenericP10.ByteControls

/-! Kernel equality of complete original propositions, including all positive,
negative, refusal, resource-order and whole-state observations. The independent
candidate execution proofs consume native semantics, not the original proofs.
`proposition` merely selects a proof term's type for this comparison. -/
namespace GenericP10.Correspondence
private def proposition {P : Prop} (_proof : P) : Prop := P

'''
    for name in names:
        text += f'''theorem {name} :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.{name}) =
      proposition (@GenericP10.ByteControls.{name}) := rfl

'''
    text += ''.join(f'#print axioms {name}\n' for name in names)
    return text+'end GenericP10.Correspondence\n', names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    original = (args.repo/SOURCE).read_bytes()
    frozen = subprocess.check_output(['git', '-C', str(args.repo), 'show', f'{census.BASE}:{SOURCE.as_posix()}'])
    if original != frozen: raise SystemExit('owner source changed; stop for relay')
    result, names = render(original.decode())
    output = args.repo/OUTPUT
    if args.check:
        if output.read_text() != result: raise SystemExit('correspondence checks are not reproducible')
    else: output.write_text(result)
    print(f'CORRESPONDENCE_SOURCE_PASS: {len(names)} exact public propositions; Lean gate separate')


if __name__ == '__main__': main()
