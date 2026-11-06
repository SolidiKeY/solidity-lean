# Primitive local assignment

`Source/Agreement/PrimitiveSlotAssign.lean` proves the fixed resolved pair
that reads the head primitive and writes it into a deeper same-typed slot.
The primitive prefix between them and suffix beyond them are arbitrary.
It consumes the existing actual getter/setter correspondence, rather than
assuming a replacement operand equality. Both concrete execution equations
retain the old head, untouched locals and actual Source journal/state.

`primitive_head_assign_step` supplies the normal-only statement obligation
for bool, uint256 and int256. `primitive_head_assign_client` produces the
initial locals relation and actual positive Source run internally from any
model state. It takes no desired read, successful run or final state premise.
Source horizon two returns the actual timeout; this is not collapsed into a
model halt. Integer operands retain their independent intrinsic range proofs.

The importing controls cover mixed bool neighbors around the written slot,
actual signed and unsigned copies for all ranged values, and the observable
reversed-copy model computation and incompatible local relation. These are
raw interpreter controls, not source-installed, native or compiler fixtures.

Independent read-only finder and skeptic read both owning files and found no
defects, without replaying checks. Their source/raw scope and actual focused
validation are recorded in the sealed packet. No new proof attempt failed.
Full lane/native fixtures were not rerun. Full Source/state/heap/storage/
installed-input/liveness/call/ABI/catch/rollback/compiler/native simulation
and the original Revert obligations remain open. H16 Source and Core ExtCall
are unchanged. Runtime versions were refreshed after the first edits; the
ordering limitation of the retained earlier authentication remains explicit.
