# Checked uint256 subtraction through selected code

`Backend/PrimitivePackets/CheckedSub` connects actual Source runtime-local
subtraction to the existing public memory compiler and its checked subtraction
guard. It adds proofs and controls, not a compiler clause or a new evaluator.

`Selected.public_selection` proves `Evm.Memory.compileVal` selects the actual
certificate used by the packet; callers supply no compiled value or desired
run. `original_guard` retains both operand loads and the existing comparison,
assertion and subtraction instruction sequence.

`Agreement.classification` applies to arbitrary in-range uint256 local operands,
Source global/frame configuration, initial Source state, and horizon `fuel + 3`.
The frame is explicitly checked. Initial `IntegerLocalFamily` correspondence
and physical `StateRepr` remain real input assumptions. The theorem derives
success when `y ≤ x` and underflow otherwise; no outcome or difference-range
premise is required. `target_underflow_iff` proves the selected physical run
reverts exactly when `x < y`, over any saved stack tail.

On success Source returns exactly `x - y` and the complete initial Source state.
Selected code pushes a representing result word, preserving all other machine
fields and the saved tail; the full physical representation still holds. On
underflow Source returns arithmetic Panic(0x11) bytes and the same Source state.
The existing target outcome is only `Evm.Out.revert`: it carries neither payload
nor final machine. No target panic-payload or reverted-state equality is claimed.

## Controls and execution

The controls instantiate independent locals over a populated caller heap,
aliases, reserved frame and arbitrary saved stack. They cover zero, equality,
maximum uint256 minus zero, ordinary subtraction, zero minus one and zero minus
the maximum. Both legacy and viaIR Source pipelines instantiate the total
classification. Negative controls reject bad local values/indices, reversed
operands, wrapped success on underflow, corrupted saved tails, insufficient
Source horizon, and empty or truncated Source panic data.

After building the five modules in import order (Source, Selected, Target,
Agreement, Controls), run
`bash tests/primitive-packets-1105/CheckedSub/run.sh` inside the existing resource
guard. The fixture runs the actual Source and selected EVM interpreters and
audits every packet declaration against `propext`, `Classical.choice` and
`Quot.sound`. Evaluator observations supplement the general kernel proofs.

This packet covers checked uint256 pure-local subtraction. Narrower widths,
effectful evaluation order, Source/frontend admission and automatic lowering,
gas/stack-resource semantics, and target panic-payload refinement are separate
obligations. No protected Source, Core syntax, compiler, profile, budget,
expected observation or trust policy is changed. Module registration, pins and
shared module-map rows remain coordinator-owned under this packet's scope.

Independent read-only finder and skeptic reviews found no correctness or
vacuity defect in the source, selection, classification and inhabited controls.
