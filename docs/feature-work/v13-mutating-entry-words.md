# Mutating entry word observations

`MutatingEntryWords.observed_activation` consumes the actual published mutating
write and allocating child-frame entry. It retains the source write, argument
and entry equations, target execution, reached StateRepr, stack, old-address
BaseExtends, exact growth-four allocator relation, saved cells and exterior
conditions. From that same representation it derives the written old-array
element n+1, child scalar n and retained alias pointer, then the existing
AbiEntry ordered two-word encoding and ExternalReturnBytes readback.

All producer index, capacity, frame separation, counter-fit and representation
premises remain explicit. Allocation preserves the already mutated heap;
original heap-content preservation is false. The concrete application discharges
these premises in the populated old-heap/stack fixture and observes [2,1].
Codec-only boundaries include zero, 300, the high bit and maximum word. Wrong
order, stale value, wrong child value and truncated bytes are rejected.

These are logical observations at child entry, not callee body execution,
return bytes, emitted unknown-memory encoding or a word/byte-machine simulation.
The full G21/G41/G42 and both backfills remain partial. G40 is abi-entry-owned,
G42.03 readonly-external-owned, and G42.05 P4-owned. Source/native lowering,
unknown-memory encoding, approved-domain/general P1, same-invocation/static-frame,
CALL/RETURNDATA, arbitrary world/resource and mandatory whole-lane gates remain
open. Historical Suite124, full1/cold124, bodyexport1, docs1 and frozen comparison1
remain failures; publication/prior finding equality is a separate result.
