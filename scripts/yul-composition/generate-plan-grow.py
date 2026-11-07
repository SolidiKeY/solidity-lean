#!/usr/bin/env python3
"""Generate enabled-plan proof steps from the existing Source horizon proofs.
No evaluator/AST/state definition or checking budget is generated or changed.
"""
from pathlib import Path
import hashlib
import re
import argparse

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check", action="store_true")
parser.add_argument("--output", default="Solidity/Source/FailureEvaluatorGrow.lean")
args = parser.parse_args()

source_bytes = Path('Solidity/Source/Horizon.lean').read_bytes()
source = source_bytes.decode()
start = source.index('structure GrowAt (G : Glob E) (n : Nat) : Prop where')
end = source.index('/-! ## Helpers keep the events -/', start)
proofs = source[start:end]
functions = ['evalE', 'evalPair', 'evalArgs', 'evalConvArgs', 'evalLoc', 'evalBuiltin',
             'evalArgsRev', 'pay', 'execS', 'forIter', 'execItems', 'runMods',
             'callInternal', 'callAddr', 'enterInstance', 'envLoop', 'dispatch']
proofs = proofs.replace('structure GrowAt (G : Glob E) (n : Nat)',
                        'structure GrowAt (G : Glob E) (points : Roadmap.Evm.FailurePoints) (n : Nat)')
proofs = proofs.replace('GrowAt G ', 'GrowAt G points ')
for name in functions:
    proofs = re.sub(r'(?<![\w.])' + name + r'(?= G\b)', name + ' (plan := some points)', proofs)
proofs = proofs.replace('grow_go [', 'grow_go [check_grow, frame_grow, emit_plan_grow, ')
proofs = proofs.replace('envLoop.eq_2 G depth pstatic none n',
                        'envLoop.eq_2 G depth pstatic (some points) n')
header = '''import Solidity.Source.FailureFrameHorizon

/-! Event growth of the actual enabled-plan evaluator. This module reuses
Source's intrinsic functions, indices and existing induction proof partition.
It introduces no alternate evaluator, NoFail assumption or execution oracle.
No horizon approximation/session consistency or P8 adequacy is asserted here.
Generated proof basis: Source/Horizon.lean SHA256 BASIS. -/
namespace Solidity.Source.FailureExecution.PlannedGrow
open EM
open Solidity.Roadmap (Address Word Bytes)
variable {E : Env} {points : Roadmap.Evm.FailurePoints}

'''.replace('BASIS', hashlib.sha256(source_bytes).hexdigest())
expected = header + proofs + '\nend Solidity.Source.FailureExecution.PlannedGrow\n'
output = Path(args.output)
if args.check:
    if not output.is_file() or output.read_bytes() != expected.encode():
        raise SystemExit('FAIL: stale generated enabled-plan proof')
    print('PASS: enabled-plan proof matches its current Horizon basis')
else:
    output.write_bytes(expected.encode())
