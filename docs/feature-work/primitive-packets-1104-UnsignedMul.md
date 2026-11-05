# Unchecked unsigned multiplication from runtime locals

`Backend/PrimitivePackets/UnsignedMul/Execution.execution` connects the actual
Source evaluator to the public memory compiler for multiplication of two
runtime locals. It covers every unsigned byte width from 8 through 256. The
operands may be any in-range integers in an `IntegerLocalFamily`; local content
and alias correspondence remain explicit input evidence.

`Selection.selectable` proves the public `Evm.Memory.compileVal` succeeds on
`UnsignedMultiplication.mulValue` applied to those locals. `selected` extracts
that actual result and `selection` proves the selection equation. The execution
theorem takes no `CompiledVal` or assumed emitted run: it combines this selected
certificate with the existing `UnsignedMultiplication.locals_transport`.

For any Source global configuration, frame and horizon `fuel + 3`, execution in
the explicitly unchecked frame returns the width-wrapped product and exactly
the initial Source state. The intrinsic evaluation and `IntValueRel` agree.
Given physical `StateRepr`, the selected code pushes a representing word over
any saved stack tail. Every non-stack machine field remains identical, and
full physical `StateRepr` holds after the push. Narrow widths use the existing
modulus cleaner after word multiplication; width 256 uses word multiplication.

## Controls

The fixtures inhabit distinct Source and intrinsic local indices above a
caller with an old allocated array, an allocator cursor, reserved memory and
an existing stack. Both legacy and viaIR Source pipelines are instantiated.
The exact compiled-run controls cover `0 * 255 = 0`, `255 * 255 = 1` and
`200 * 2 = 144` at width 8, and `(2^256 - 1) * 2 = 2^256 - 2` at width 256.
Every legal width also has an inhabited exact-zero execution with physical
preservation. Wrong cleaning actually executes the width-256 selected code
on the narrow fixture and yields 400 rather than 144. A corrupted saved tail
is refused; a Source horizon of two yields the actual timeout.

After building `UnsignedMul.WidthControls` and `UnsignedMul.WideControls`, run
`bash tests/primitive-packets-1104/UnsignedMul/run.sh` inside the usual resource
guard. It prints actual Source and emitted-interpreter observations and audits
every declaration under the packet namespace. The allowed axiom set is
`propext`, `Classical.choice`, `Quot.sound`; sampled observations supplement
kernel-checked general and inhabited execution proofs.

## Boundary

This packet proves unchecked pure-local value multiplication. Pipeline
quantification does not establish effectful operand ordering. Checked
multiplication, declaration/profile admission, automatic Source-to-intrinsic
lowering, general Source heap/world correspondence and a complete compilation
pipeline remain outside this result. No Source evaluator, compiler clause,
intrinsic representation, budget, trust policy or refusal policy is changed.
All five modules are published and registered on master as of `89373e34`.
The evaluator fixture and this documentation remain worker-owned artifacts;
shared generated roots and maps are not edited by this packet.
