# Source Bool slice to intrinsic allocation

`Backend/MemoryOps/SourceCalldataBoolSliceNative.lean` adds
`SourceBoolStructAt.slice_bool_copy_native`. It composes the actual slice/window
law from `Backend/MemoryOps/SourceCalldataBoolSlice.lean` with the existing paired
copy producer in `Backend/MemoryOps/SourceCalldataCopy.lean`.
Here native means the EXISTING intrinsic Heap.alloc operation; no emitted word,
byte allocator, copy loop or external EVM execution is proved or assumed.

INITIAL evidence is the independently established named struct/child observer,
Source MemOK, typed root/start/finish local alignments and validity of the
computed selected native window length. There is no supplied payload, desired
postrelation, allocation run or global address injection. Parent reference
length need not be artificially capped to establish a smaller valid window;
the size premise is native MObj validity, not a Source admission restriction.
The computed bounds cases retain actual Source state, with no allocation suffix.
Valid slicing shifts the decoder to off+32*start and stop-start, using the actual
immutable raw calldata decoder. Successful Source.allocRef/native Heap.alloc,
Keeps, old named parent/tag/selected-child observations, every initially
represented old Boolean alias, fresh identity/map extension and Source
MemOK/locals/world/ex/events/logs/fnLocals frames follow from the old producer.
The original decoder/allocation proofs are reused, not reimplemented.

The additive controls in `Backend/MemoryOps/PhysicalStructChildControls.lean`
reuse the populated named parent with tag7, LEFT[T,F,F], RIGHT[F,T,F] and old
aliases. A noncanonical64-byte prefix precedes words[1,0,1]. Root offset64,
start1 and end3 cause actual decoding at offset96 to yield[F,T]; wrong offset0
really rejects. BOTH pipelines execute the slice conversion, obtaining actual
Source and intrinsic fresh identity3. Old identities2/0/1, full object records,
old lengths3/3, tag/parent-child fields and all Source locals/world are retained.
The INITIAL four-address table includes get3=none; reached next4 and complete
final records are explicit. Fresh reads return true at1 while retained LEFT
returns false, so stale identity is observable. End2 gives Source index panic
and intrinsic none, with distinct scope from slice-bound revert[]. Literal
empty[3:3] succeeds. Reversed start4/end3 and end4 beyond declared length3 reject
through the NEW generic classifier; horizon2 times out without a copy.
Generic toEnd support is proved; only explicit-end controls are newly inhabited.
Every previous vector/body/guard is byte-preserved. Existing emitted-word
vectors remain their earlier evidence; no new emitted allocation state is
invented for this component.

Slice bounds concern the declared calldata reference length, not proof of raw
entry authenticity or a raw-byte span check. Standalone cdToMem uses cdWordAt's
existing zero-padding; no truncated-input rejection or replacement guard is
asserted. Actual entry/span refusal remains the existing cdTail/ABI producer
obligation. Source failures do not establish transaction rollback.

Six exact measured standard-only guards accompany the new law and five clients.
General ABI/native writer/compiler correspondence, physical memory, arbitrary
reference/recursive graphs, deep copy/liveness/all-profile allocation failure,
reserved producers and final Source/V10/target composition remain open.
