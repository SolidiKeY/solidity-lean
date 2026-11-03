# Executable bytecode selection

`Solidity/Backend/Selection/**` states the G45 obligations for turning the
compiler IR into executed bytecode. At this checkpoint both modules are
statements only: certificate fields are obligations, and no inhabitant or
theorem is claimed by declaring a structure.

## Interface

`Interface.lean` fixes the contracts for instruction selection (with physical
operand refusal), frame preservation over every untouched suffix, finite
structured execution of the existing `Block`, execution at a real assembled
byte placement, and composition that ties assembly, encoding and behaviour to
the same emitted program. `FrameCertificate.prefixes` is conditional on `Scalar.stackBound` and follows
from the existing `Scalar.prefix_capacity`, so it does not yet impose the
G45.02 physical capacity; that field is still to be strengthened.
`StructuredExec` uses the existing numeric
evaluator for leaves and conditions, records the actual intermediate stacks
and covers arbitrary finite loop bodies. It does not classify divergence or
change Source evaluation horizons. A decoder roundtrip alone is never treated
as executable behaviour.

| Item | Existing result reused | Remaining obligation |
|---|---|---|
| G45.01 | `Scalar.selectUnary`, `selectBinary`, `selectChecked`; `Scalar/Typed.lean` certificates, `Scalar/Values.lean` composition | Selection from `Evm.Instr` with explicit unsupported instructions |
| G45.02 | `Scalar.step_frame`, `run_frame`; `Scalar.Heights`; `LabelExec.arity_domain` | DUP/SWAP/POP index translation, frame expansion, physical capacity |
| G45.03 | `Block.expand`, `LabelExec.Assembly`, `Loops.loop_header`/`loop_backedge`, `Boundaries` | Whole branch/sequence execution at true byte offsets |
| G45.04/.05 | `assemble`, `assemble_eq`, `assemble_pushTag`, `decode_encode` | Composition of these, without equating roundtrip with execution |
| G45.06 | The layers above | Same-program control/assembly/bytes composition |

Partial scalar-sequence and artifact results from the V14 branch (not on
master) are to be ported under Selection rather than reproved; none is ported
yet.

## Premises

`Premises.lean` names the external inputs as typed parameters, never axioms:
G24.03 source-to-IR preservation, G45.05-BR reachable-state decoder agreement
(an empty reachable set cannot discharge it, since the entry is reachable),
and the G49.02 runtime-consumer statement on the exact composed bytes. The
consumer statement is not a G49 proof.
