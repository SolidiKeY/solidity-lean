#!/usr/bin/env python3
"""Generate proof-only enabled-plan event-prefix induction, with exact basis binding."""
from pathlib import Path
import argparse
import hashlib
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true')
parser.add_argument('--output', default='Solidity/Source/FailureEvaluatorApprox.lean')
args = parser.parse_args()
raw = Path('Solidity/Source/Horizon.lean').read_bytes()
source = raw.decode()
start = source.index('structure ApproxAt (n : Nat) : Prop where')
end = source.index('\nend\n', source.index('theorem approxAt (G : Glob E)', start))
proofs = source[start:end]
proofs = proofs.replace('structure ApproxAt (n : Nat)',
    'structure ApproxAt (G : Glob E) (points : Roadmap.Evm.FailurePoints) (n : Nat)')
proofs = proofs.replace('ApproxAt G ', 'ApproxAt G points ')
proofs = proofs.replace('growAt G ', 'PlannedGrow.growAt G (points := points) ')
functions = ['evalE','evalPair','evalArgs','evalConvArgs','evalLoc','evalBuiltin',
             'evalArgsRev','pay','execS','forIter','execItems','runMods',
             'callInternal','callAddr','enterInstance','envLoop','dispatch']
for name in functions:
    proofs = re.sub(r'(?<![\w.])' + name + r'(?= G\b)', name+' (plan := some points)', proofs)
proofs = proofs.replace('approx_go [', 'approx_go [frame_approx, ')
proofs = proofs.replace('[heapPut_grow,', '[check_grow, frame_grow, emit_plan_grow, heapPut_grow,')
proofs = proofs.replace('Approx.attempt_bind (ih.dispatch _ _)',
                        'Approx.attempt_bind (frame_approx _ (ih.dispatch _ _))')
header = '''import Solidity.Source.FailureEvaluatorGrow

/-! Closed event-prefix approximation for the actual fixed-plan mutual
Source evaluator. All seventeen functions execute the same explicit plan.
No NoFail, execution oracle or supplied evaluator agreement is assumed.
This is not a fixed-plan session, deployment or P8 realization theorem.
Proof basis: Source/Horizon.lean SHA256 BASIS. -/
namespace Solidity.Source.FailureExecution.PlannedApprox
open EM
open Solidity.Roadmap (Address Word Bytes)
variable {E : Env} (G : Glob E) {points : Roadmap.Evm.FailurePoints}

'''.replace('BASIS',hashlib.sha256(raw).hexdigest())
expected = (header + proofs + '\nend Solidity.Source.FailureExecution.PlannedApprox\n').encode()
output = Path(args.output)
if args.check:
    if not output.is_file() or output.read_bytes() != expected:
        raise SystemExit('FAIL: stale generated enabled-plan approximation proof')
    print('PASS: enabled-plan approximation proof matches exact basis bytes')
else:
    output.write_bytes(expected)
