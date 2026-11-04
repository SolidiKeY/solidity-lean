# Reached alias/write and scalar read

Module `Solidity.Backend.MemoryOps.SourceUintAliasWriteRead` proves
`Solidity.Backend.MemoryOps.source_uint_read_into_objects_word` using actual
Source array reads and scalar assignment, intrinsic assignLocal and published
Objects read/local-store certificates. The read value is computed from the
INITIAL typed heap contents and bound; no desired read/run/poststate premise
is supplied. Result/index/RHS scalar locals may alias, because storing follows
reading. Strong Objects/allocator and heap/world/stack/free-pointer frames are
retained, with actual Source scalar locals and MemOK derived.

`Solidity.Backend.MemoryOps.source_uint_alias_write_read_word` consumes initial
root/index/RHS alignment, SourceUintMemoryAt/MemOK, true selected bounds, strong
Objects.StateRepr/AllocatorRepr, positive base and valIn. Existing alias/write
execution derives the SAME reached object, value, length and operands used by
the read. The conclusion contains Source expressions and ONE three-statement
Items execution at sufficient horizons h+5/h+4/h+3 and Items h+7 with original
parameter count; ONE intrinsic Prog; prefix/suffix executions and the WHOLE
existing word append. No intermediate relation, successful suffix or final
agreement is assumed. Runtime lengths and canonical uint256 values remain
quantified without admission caps, new semantics or a changed representation.

The actual both-pipeline client writes42 through a rebound pointer, then reads
index1 and stores42 into that SAME index local. This local value update follows the actual read and consumes the write's
reached state; the typed context is unchanged. Full initial/alias/written/read twenty-word vectors, Source/native
object tables, locals/world/caller frames, saved stack and allocator are kept.
Distinct and self reference identities are inhabited; old aliases and unrelated
objects follow the proved frames. The separate stale-old-object Source read
returns0 instead of the selected42. The following read now uses index42 and
has exact Source index panic, native value failure and whole word append revert.
This is a separate reached expression/value boundary, not a four-statement
Source Items theorem or a post-error target machine/rollback claim. Source
Items horizon6 retain the actual42 heap write before scalar assignment times
out, exposing only globals in the error outcome. Earlier controls are intact.

Exact headline guards remain standard-only. Emitted code realizes the discarded
expression statement; no extra emitted expression-result theorem is asserted.
Kernel/symbolic-word evidence is separate from external solc/EVM and physical
byte adequacy. Original full private wrapper/TestSuite/strict/corpus closure,
raw global docs/inventory failures and general Source/V10/world/representation/
copy prerequisites remain open. No original goal, budget/profile/ownership or
semantic decision changes, and no new cold timing coverage, follow here.
