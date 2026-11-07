# Dynamic uint aliasing with strong object representation

`Solidity/Backend/MemoryOps/SourceUintAlias.lean` adapts the published Source
local assignment and Objects pointer-rebinding certificate to genuine dynamic
uint arrays. It consumes an INITIAL SourceUintMemoryAt relation for the SAME
selected native reference; independent unrelated pointer runs are insufficient.
No constructor, allocator, compiler, graph model or semantics is duplicated.

`source_uint_alias_word` proves actual Source expression/statement, intrinsic
rebindMem and existing aliasLocalCode execution. It derives the reached contents
observer, MemOK, local identity, unchanged heaps/other locals, strong Objects
StateRepr and AllocatorRepr, KeepsAllocator, saved stack and free-pointer frame.
The Source type remains array memory uint256 none; runtime capacities of old
and selected objects may differ. There is no global Source address-injectivity
premise or assumed final agreement. Initial pointer alignment, representation,
allocator and positive-base premises remain explicit.

`source_uint_alias_read_bounds_word` derives the reached index/local alignment
and actual selected capacity from that alias output. One Source Items program
executes alias then read and returns exact Source index panic. The matching
native value evaluation errors and the WHOLE existing alias/read word append
reverts. Strong Objects/allocator facts are retained for the successful alias
prefix; no target suffix machine, rollback or matching panic payload is claimed.
Sufficient Source horizons are alias expression fuel+4, read fuel+3, Items fuel+6,
with original parameter count. The compiled index fragment's valIn premise is
kept. These are not minimal-fuel or admission bounds.

Additive controls in
`Solidity/Backend/MemoryOps/SourceUintReadAssignmentControls.lean` preserve every
prior body/vector. Both pipelines rebind an old length3 root to an existing
length2 neighbor while retaining the old alias. Complete ordered 20-word vectors
include local pointer replacement, all three headers/payloads, maximum word,
guard, unused cell, free pointer and saved stack. Complete Source/native object,
local and world observations preserve all contents. Index2 rejects at the new
root but the actual retained old alias reads maximum in Source AND the word
model. Self-alias is a no-op; low Source alias fuel times out before rebinding.

The initial finite fixture is inhabited, not a public capacity restriction.
General graphs, reference copies, all-profile construction/allocation failure,
physical byte memory, Source admission, final Source/V10/target/world and external
compiler/EVM correspondence remain open. Symbolic word execution is distinct
from physical-byte or external compiler execution.
