# Dynamic uint alias followed by a primitive write

`Solidity.Backend.MemoryOps.source_uint_alias_assign_word` consumes INITIAL local
alignment, Source MemOK and SourceUintMemoryAt, actual selected capacity,
strong Objects.StateRepr/AllocatorRepr, positive base and index/RHS valIn.
The Source type remains dynamic uint256 memory; no fixed-type erasure occurs.

It derives the SAME reached local/observer from source_uint_alias_word,
then the Source primitive write and native writeAddr from write_observed.
The existing strong Objects.PtrFrag.write consumes those actual outputs.
The conclusion contains one Source RItems execution (original parameter count),
one native Prog and the WHOLE aliasLocalCode ++ uintAliasWriteCode run.
Sufficient horizons are alias expression h+4, assignment expression h+3 and
Items h+6; these are not minimal fuel, admission or budget claims.

The reached relation, MemOK, primitive set contents, unrelated native objects,
different Source addresses, other Source locals, world/events/logs/fnLocals,
strong representation/allocator, saved stack and free pointer are consequences.
No desired final relation, successful suffix, global injectivity or copied
allocator/compiler algorithm is a premise. The write code is the literal
value/pointer/index/write sequence of the published strong certificate.

The populated control quantifies both original pipelines and self/distinct
identity. It rebinds an old length-three object to an existing length-two
neighbour and writes index one with 42; retained LEFT stays unchanged in the
distinct case. Self alias mutates LEFT while the unrelated right object stays
unchanged. Earlier complete ordered vectors and guards remain byte-preserved.
The new client retains an existential final target and payload/frame facts;
new complete ordered Source/native/final 20-word vectors, discriminator and
short-horizon extensions remain pending, rather than claimed by this client.

Focused kernel checks and exact standard-axiom guards validate these laws.
This is an incremental partial interface, not end-of-lane validation, a raw
global docs/inventory pass, compiler/EVM test, physical-byte store theorem,
general allocation/copy/reference graph theorem, or whole-source closure.
Original full-wrapper/TestSuite/strict/corpus closure and genuine Source/V10,
world/representation/reserved-copy producers remain open. No new cold timing
coverage is claimed. Prior failures/seals and goal status remain unchanged.
