# G35-BYTESN-RAW-1105

Assigned base: b86ae4568cef6d6226f4d170360bbb089debe3fb. This disjoint
rebalance does not close or alter the original Selection queue, its failed
full validation, premises or sealed evidence.

Modules for coordinator registration (no shared registry edits here):

- `Solidity.Backend.CalldataPackets.RawBytesN.Interface`
- `Solidity.Backend.CalldataPackets.RawBytesN.Execution`
- `Solidity.Backend.CalldataPackets.RawBytesN.Controls`

The signature checkpoint is d4e6eb0c. The implementation follows the published
RawUint template and reuses Source.decodeWord, cdToMem, cdTail, allocRef and
MemoryOps.source_mapM_lift_run; none of those modules is edited. For every
intrinsic bytesN width (1 through32), decode_word exposes the existing exact
low-byte-zero check. copy_run computes its outcome from the raw frame, with
no supplied successful decoding/run premise. Failure preserves the complete
input state. Success allocates precisely the actual decoded values and
preserves every address other than heap.next and all non-heap state.

The ordered entry theorem retains short-head, length>=2^64 and span checks,
then validates each element before allocation. Its frame binding requires
exactly four selector bytes followed by the same argument bytes; its payload
is computed from those bytes. Standalone copying retains zero padding beyond
EOF; this does not bypass entry bounds.

Controls cover a nonempty existing heap, unequal ordered words, a later dirty
low byte despite a valid entry span, wrong order, empty allocation, zero
padding, bytes31 refusal versus bytes32 acceptance, successful selector-bound
entry and state-preserving refusals for all three entry guards. These are
kernel proofs of Source operations, not external runtime tests or physical
EVM/compiler adequacy. No new foreign premise, Source edit, ExtCall change,
axiom, native_decide, heartbeat increase or exclusion is introduced.

Independent read-only finder and skeptic found no soundness defect. Their
coverage request for oversized-length and truncated-span controls is addressed;
the preservation prose now explicitly excludes heap.next. Final diagnostic,
serial module timings and touched/checkpoint gate outcomes belong to the
sealed handoff. Shared imports, pins and module-map are coordinator-owned;
registration-dependent failures must remain visible rather than be waived.
