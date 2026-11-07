# Checked uint256 multiplication

The six CheckedMul modules follow the unchanged CheckedAdd template. Source
proves actual checked local evaluation; Selected.public_selection proves public
Evm.Memory.compileVal selection, and original_guard exposes its exact existing
operand loads and multiplication/division/zero guard. Target derives actual
selected execution from the existing expression certificate.

Agreement.success and overflow combine actual Source and selected execution
under IntegerLocalFamily and full StateRepr. Arbitrary bounded uint256 operands
are admitted. source_overflow_exact and target_overflow_exact classify failure
exactly when the mathematical product exceeds uint256 maximum. Unsigned
nonnegativity discharges the lower bound. No selected code, desired execution
or desired poststate is supplied as a premise.

Success preserves exact Source state and every target machine field beneath
one product word over an arbitrary saved tail. Source overflow retains exact
arithmetic panic bytes and state. Target failure remains coarse revert: no
payload or post-failure machine is asserted. Frames and evaluator pipelines
remain arbitrary; checked mode is selected explicitly.

Populated gives a concrete full representation with two aliases and an
independent nonempty array. Controls cover 7×9, zero on either side, maximum×1,
maximum×2 overflow and maximum² overflow. Joint success/overflow and zero/max
controls quantify over both pipelines. Wrong-value and wrong-index
correspondence are refused; low fuel remains timeout. Panic bytes are neither
empty nor truncated.

This is local-expression agreement under explicit initial local correspondence
and full representation, not frontend lowering, physical input origin, whole
bytecode/EVM adequacy or failure-frame transport. No compiler arm or Source
semantics changes. The first broad template import reached an unchanged
11,000-heartbeat timeout in Evm/Correct's statement proof. The packet now uses
existing ValFrag.correct directly and an independent concrete fixture. This
narrows imports without weakening any theorem or changing the producer.
Failed logs remain retained. Read-only finder and skeptic found no defect.
Registration and area-row proposals are supplied in the scoped test handoff;
shared roots and inventories are left to the coordinator.

Final single-module builds pass: Source 1.527 s, Selected 1.221 s, Target 1.731 s,
Agreement 1.832 s, Populated 1.532 s and Controls 4.671 s. Peak aggregate RSS
is 818,216,960 bytes. No owned module exceeds 60 seconds. The earlier broad
target build failed after 119.241 s while rebuilding dependencies, including
the published statement correctness heartbeat failure; it is not a passing
measurement. Successful printed inventories contain only propext,
Classical.choice and Quot.sound or subsets. Gate/checkpoint outcomes remain
separate from these successful owned checks.
