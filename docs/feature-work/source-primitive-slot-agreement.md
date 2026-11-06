# Primitive local initialization agreement

`Source/Agreement/PrimitiveSlot.lean` pairs existing intrinsic Source/model
indices beneath an arbitrary primitive prefix. Selected getters preserve
`PrimitiveRel`; setters retain the remaining locals when supplied related
replacement values. This is local transport, not a Source assignment producer.

`primitive_read_init_step` proves the actual resolved declaration pair for
bool, uint256 and int256. Source self-conversion is proved separately for
those three types; no range evidence is dropped. Both actual interpreter
initialization equations are proved, including the Source journal/state.
The concrete importing client derives the initial relation and Source run
from any model environment instead of assuming a desired reached state.
Unsigned and signed copy controls retain the actual integer, and a different
unsigned result is refused. Source horizon one actually times out.

This does not supply whole-step simulation, source admission/installation,
canonical calldata, heap/storage/liveness, call/ABI/catch/rollback, compiler
or native correspondence. H16 Source producers and Core ExtCall are unchanged.
Original Revert obligations and global documentation failures remain open.

The proof attempts retain three failed attempts: the initial generic
self-conversion evidence and then the Source initialization equation did not
reduce before primitive splits, and direct
dependent elimination at a fixed unsigned value failed. The repairs factor
self-conversion and relation-to-produced-value equality. The automation
scratch examples and MCP candidate result are preserved with raw logs.
Focused owning diagnostics, actual importing closure, standard axiom audit
and selective independent source/raw reviews are recorded in the sealed packet.
No full checkpoint/native fixture rerun or cold-build timing is claimed.

Independent read-only finder and skeptic reviews read both complete source
files and selected raw diagnostics/build/audit records; neither replayed
checks. They found no defects. Fresh static checks passed. Full-lane gates
were not repeated for this bounded checkpoint. Runtime versions were
recaptured after the first edits, not before; the earlier authenticated
runtime identity is retained, and no stronger ordering claim is made.
