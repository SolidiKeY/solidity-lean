# Physical consequence of the mutating write prefix

`MutatingWritePhysical.write_prefix` consumes the actual selected mutating
source/word-machine write. It preserves its reached typed StateRepr, exact
zero-growth allocator relation and word footprint. An INITIAL P6 WordFrame,
with explicit stronger physical bound `32*cell+32 ≤ W`, yields the reached
physical frame after the corresponding existing scaled byte MSTORE, complete
32-byte readback through the existing AbiEntry codec, and all exterior bytes.
No reached physical representation or desired execution is assumed.

The byte MSTORE is a separate existing local operation with an arbitrary stack
tail. This is not identity of emitted word code and physical byte code, physical
execution of the subsequent allocation/frame entry, or an unknown-memory ABI
encoder. The primitive counter's full unsigned value is retained without a
byte-range restriction. Stronger physical span fit does not follow from word fit.

The concrete application starts from two live represented cells: old array
cell 18 contains 9, distinct older object cell 21 contains 4. The actual selected
write changes the former to 2. Its byte image changes at byte offset 576;
offset 672 still contains 4, with the byte-store stack tail 77 retained. Complete
old/new/neighbor bytes and wrong-scale, stale-value and word-fit/byte-fit controls
are kernel checked. Six axiom reports are explicitly guarded.

G21, G41, original G42.01-.02, G42.04, G42.06 and Backfills A/B remain partial.
G40 belongs to abi-entry, G42.03 to readonly-external, G42.05 to P4. General
source/native lowering, runtime ABI encoding, approved-domain/general P1,
operational same-invocation/static provenance, CALL/RETURNDATA, arbitrary
world/resource composition and final whole-lane gates remain open. No producer
premise, profile, semantics, fixture, budget or persistent-goal status changes.
Historical Suite124, full1/cold124, bodyexport1, docs1/frozen comparison1 remain
failures; publication/prior finding equality is separate. Earlier observation
sources and sealed outputs are unchanged, not claimed as freshly rerun here.
