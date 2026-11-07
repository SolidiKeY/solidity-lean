#!/usr/bin/env python3
"""Proof-only enabled-plan full-result stability induction; no evaluator changes."""
from pathlib import Path
import argparse
import hashlib
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true')
parser.add_argument('--output', default='Solidity/Source/FailureEvaluatorStability.lean')
args = parser.parse_args()
raw = Path('Solidity/Source/Horizon.lean').read_bytes()
source = raw.decode()
start = source.index('structure BelowAt (n : Nat) : Prop where')
end = source.index('\nend\n', source.index('theorem belowAt (G : Glob E)', start))
proofs = source[start:end]
proofs = proofs.replace('structure BelowAt (n : Nat)',
    'structure BelowAt (G : Glob E) (points : Roadmap.Evm.FailurePoints) (n : Nat)')
proofs = proofs.replace('BelowAt G ', 'BelowAt G points ')
functions = ['evalE','evalPair','evalArgs','evalConvArgs','evalLoc','evalBuiltin',
             'evalArgsRev','pay','execS','forIter','execItems','runMods',
             'callInternal','callAddr','enterInstance','envLoop','dispatch']
for name in functions:
    proofs = re.sub(r'(?<![\w.])' + name + r'(?= G\b)', name+' (plan := some points)', proofs)
proofs = proofs.replace('below_go [', 'below_go [frame_below, ')
proofs = proofs.replace('Below.attempt_bind (ih.dispatch _ _)',
                        'Below.attempt_bind (frame_below _ (ih.dispatch _ _))')
header = '''import Solidity.Source.FailureScopeStability

/-! Closed equality-or-timeout induction for the actual enabled-plan
mutual evaluator. Full results include locals, state and cursor. No external
execution oracle, NoFail or fragment premise. This does not establish event
prefix approximation on timeout or fixed-plan session/P8 adequacy.
Proof basis: Source/Horizon.lean SHA256 BASIS. -/
namespace Solidity.Source.FailureExecution.PlannedBelow
open EM
variable {E : Env} (G : Glob E) {points : Roadmap.Evm.FailurePoints}

'''.replace('BASIS',hashlib.sha256(raw).hexdigest())
expected = (header + proofs + '\nend Solidity.Source.FailureExecution.PlannedBelow\n').encode()
output = Path(args.output)
if args.check:
    if not output.is_file() or output.read_bytes() != expected:
        raise SystemExit('FAIL: stale generated enabled-plan stability proof')
    print('PASS: enabled-plan stability proof matches exact basis bytes')
else:
    output.write_bytes(expected)
