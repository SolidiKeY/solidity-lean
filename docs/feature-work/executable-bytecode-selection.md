# Executable bytecode selection

`Solidity/Backend/Selection/**` states the G45 obligations for turning the
compiler IR into executed bytecode. At the initial checkpoint the interface modules were
statements only: certificate fields are obligations, and no inhabitant or
theorem is claimed by declaring a structure.

## Interface

`Interface.lean` fixes the contracts for instruction selection (with physical
operand refusal), frame preservation over every untouched suffix, finite
structured execution of the existing `Block`, execution at a real assembled
byte placement, and composition that ties assembly, encoding and behaviour to
the same emitted program. `FrameCertificate.prefixes` is conditional on `Scalar.stackBound` and follows
from the existing `Scalar.prefix_capacity`, so it does not yet impose the
G45.02 physical capacity; V1 must not supply a G45.02 physical-capacity result. V2 below supplies the stronger contract.
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

## Interface V2: non-vacuous obligations

The V1 frame-prefix field does not certify physical capacity. In particular, the
empty tail must be admitted. The original uniform gasless frame law is retained,
without claiming capacity for larger tails. No G45.02 capacity result may rely
on the V1 frame contract.

PremisesV2.lean requires a nonempty compiler observation relation. Its runtime
consumer also requires an admitted numeric-stack/frame witness with an actual
successful Evm.run equation, independently
of its implication premises. Thus relation := False cannot make either V2
contract trivially inhabited. Nonemptiness alone is not source-evaluation
coverage: the concrete source observation relation and its preservation are
still the G24.03 producer's responsibility. The decoder and exact-byte control
contracts are reused, and no G49.02 theorem is proved here.

V14 branch proofs are not on master; no master theorem is attributed to them.

V2 signature finder/skeptic reviews confirmed empty-tail admission and rejection
of relation := False. Skeptic additionally found that a bare relation witness
could name an incorrect final IR stack; strengthened it with the actual IR-run
equality. A usable runtime result still requires the explicit compiler/decoder
premises; neither a witness nor nonemptiness proves source-evaluation coverage.

### V2 kernel consequences and controls

FrameCapacityV2.lean derives actual empty-tail capacity, capacity of every
admitted prefix, and final output bounds from the required V2 fields. Its
identity and DUP1 certificates are inhabited and preserve arbitrary protected
tails; DUP's physical room domain includes its extra word.

InterfaceV2Controls.lean constructs the exact old defect: 1025 actual PUSH0
instructions satisfy the V1 gasless frame contract. Boundary controls check DUP
at heights 1023 and 1024. Nonempty no-op compiler and valid IR-witness controls,
false compiler/runtime relations, and the incorrect final-IR-state control cover
the premise changes. They are not a G24.03 or G49.02 theorem.

Limits (review): `peak` need not be least, so a certificate with
`peak := 1024 - input.length` claims capacity only for the empty tail.
`CompilerPremise` V2 is inhabited only by source-independent relations such as
`identityCompiler`; nonemptiness is not coverage. No `RuntimeConsumer` V2
instance exists yet; `runtime_witness_inhabited` shows only that its witness
domain is nonempty.