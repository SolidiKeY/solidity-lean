# Physical memory views, adapters and recursive loop transport (VY2)

From the vy2-physical lane: Yul memory views (`Yul/Views/**`), Source/frame
adapters onto the P6 interface (`Yul/Adapters/**`), the P5 loop horizon and the
recursive/mixed loop compiler extension (`Evm/MemoryLoop*Horizon*`,
`Evm/MemoryRecursive*`, `Evm/MemoryMixedLoop*`).

## Proved

- Loop horizon (P5): `Evm/MemoryLoopHorizon.lean`,
  `Evm/MemoryLoopFiniteHorizon.lean`: all-depth and finite-horizon loop
  transport over `TLoop.iterN`, with controls.
- Recursive and mixed loops: certificates, compiler and room metadata
  (`MemoryRecursiveCert`, `MemoryRecursiveCompile`, `MemoryRecursiveRoom`),
  closed mutual correctness (`MemoryRecursiveSound`: `ProgCert.profile_sound`,
  so the top-level `StmtCert.correct` needs no lifting premise), outer-loop
  lifting, nesting and budgets, mixed-body loop transport.
  `MemoryRecursiveDispatch` tries the existing compiler first and falls back on
  refusal; it is additive and not wired into `Compiler.compile`. The recursive
  allocation control derives its one-word demand bound from the actual
  computed certificate and discharges allocator room using the represented
  cursor; both recursive and mixed examples now have concrete room proofs.
- Views: byte/word views and codecs, placement and images, scalar codecs,
  static/dynamic `uint` arrays, members, pointers, byte objects, heap
  inventories and preparation, joint and aggregate views. `ByteView` keeps its lightweight API; `Adapters/MemoryBytes` proves exact
  operation agreement with the existing `Environment.Memory` byte map.
- Adapters: `P6Memory`, `P6ByteMemory`, `P6Inputs`, `MemoryAgreement` relate
  Source and frame memory to bytes for dynamic `uint256` arrays only;
  `FrameMem.st` is not identified with the changed Source heap. Frame
  construction, writeback, physical objects and calldata slices
  (`FrameHeap`, `HeapWriteback`, `ObjectWriteback`, `PhysicalObject`,
  `SourceSliceFrame`, `ImageIdentity`). They use the current `Source.Fr` with
  `cd`.

`MemoryLayoutObligations`, `MemoryWritebackObligations` and
`AllocationRefines` are interfaces with no instance and no consumer.

## Open

Other element types, a Source-heap identification for `FrameMem`, wiring the
recursive dispatch into the compiler, allocation bounds for arbitrary recursive programs,
G36.02 recursive/enclosing transport.

## Canonical nominal memory

`Views/NominalMemory` adds UDVT word decoding through the actual underlying
canonical scalar codec, preserving nominal type indices. Its successful words
reencode exactly; encoded supported values decode identically. Array preparation
uses the existing decoder and actual `Source.heapPut`; every original heap typing
is preserved through its complete success/error result. Declaration lookup is
checked separately from the layout fallback. Controls inhabit a real allocated
heap and observe updates through two actual Source aliases.

The explicit expected array length is a preparation guard, not proof of old
length, capacity or valid output placement. Whole-state unchanged identity is proved from the actual old typed heap data,
declaration and exact header/word encoding facts. For same-length writes to an actual old typed array, output placement is
constructed with unchanged addresses, shapes and free choice. Types, next,
boundedness, unrelated cells and non-heap source fields are preserved; exact
typed payload readback matches the raw canonical words. A changed-snapshot
kernel control inhabits this operation. General nominal allocation provenance and universal nominal heap agreement
remain open. Dirty
words are not cleaned or assigned source/Yul failure semantics by this codec.

`Views/NominalRetained` extends canonical nominal dynamic arrays within an
actual `RetainedAllocation`. Header size is checked against the original
allocated shape, including the length word. Successful preparation derives the
real source write and a current placement with the new length plus original
retained provenance. Unchanged snapshots preserve the complete source state;
every original heap typing survives the complete source result. Kernel controls prove actual shrink-to-zero and regrowth. Runtime controls
observe the same nonzero raw tail, two source aliases, coherent free/zero
words, source type-error and preparation boundaries.
This is canonical snapshot preparation with explicit old typed contents and
retained ownership, not general allocation, dirty-word or assembly adequacy.

## Byte API agreement

`Adapters/MemoryBytes` proves full-map snapshot-copy equivalence between
`Views.copyBytes` and backend `writeBytes` of the old `readMemory` result.
Byte update and read APIs agree definitionally; unchanged snapshot writeback
is identity for the whole mathematical byte map, without size or canonicality
restrictions. This keeps backend imports out of the lightweight Views module.

The actual P6 `copySnapshot` and `store8` byte projections now agree with
`Views.mcopy` and `Views.mstore8`. P6 self-copy uses the common identity proof.
Nonempty self-copy can still change access metadata; physical spans and fit
premises remain unchanged. These laws do not supply target MCOPY execution,
allocation refinement or identification of carried intrinsic state with bytes.

## Recursive one-turn room

`Evm/MemoryRecursiveOneTurn` reduces future-prefix allocation room to initial
body demands when the actual successful body forces its next condition false.
The public full-loop transport uses the real recursive certificate's derived
profile soundness. It does not impose a loop horizon, alter admitted programs or
assume target/source adequacy. The initial body-demand room remains explicit.
`MemoryRecursiveDemandViews` exposes actual constructor cases without assuming
code-list append injectivity. `MemoryRecursiveDemandBounds` combines the finite
head's computed source `prefixBudget`, nonallocating tails and real stopping facts.
`MemoryRecursiveAllocation.demand_bound` proves every demand of its computed
certificate is at most one word. `actual_room` then uses the represented cursor
and `one_word_input`; `correct actual_room` is a closed kernel transport for that
example. This does not discharge room for arbitrary allocating programs.

## Physical byte-write order

`Adapters/P6ByteWriteOrder` composes two actual `writeSpan` operations, deriving
capacity transport for the second span. Disjoint byte regions commute on the
complete existing P6 frame: byte data, logical carrier, key, capacity and exact
high-water count. Frame extensionality explicitly requires metadata as well as
the complete byte image; no byte-only equality is promoted to frame equality.
Empty spans are included even when their offsets lie inside the other span.

Kernel controls instantiate complete-frame order equality for both pipeline
tags and the empty-inside case. Separate runtime controls observe nonzero raw
bytes, exterior preservation, access growth and the expected order sensitivity
of overlapping writes. No overlap is refused by the operation. These are
physical side-frame laws, not typed Source-heap writeback, target execution, gas
accounting or global storage/transaction journal adequacy.

Same-span writes also satisfy full-frame last-write replacement (`writePair_overwrite`). The earlier payload disappears, while unknown exterior bytes and the real access accounting are preserved. The law includes empty spans; it is a physical frame law, separate from Source-heap or transaction-journal adequacy.

`FrameHeap.residual_span_unchanged` connects an actual bounded P6 `writeSpan` on a computed complete heap image to whole Source-state writeback identity. It also proves the complete reached raw map equals that byte write, so modified residual bytes are retained. The canonical support, initial MemOK, Placement, retained allocation, physical capacity and object-complement premises remain explicit. Object separation alone does not establish reserved-word safety, allocation reachability or language admission. The mixed six-root control exercises both pipeline tags.

`FrameHeap.calldata_residual_unchanged` composes the actual bounded Source calldata-slice producer with the computed physical heap image. It derives source success, exact copied bytes/readback and complete Source-state writeback identity, using the real calldata reference bound and destination length. A destination-size mismatch remains successful Source evaluation with preparation `None`; this theorem does not reclassify failures or establish general source/opcode/allocator adequacy.

`P6Inputs.source_hash_local` proves the complete actual Source `keccak256` builtin result/state for a memory-byte local and real heap lookup at every horizon `n + 3`. `copied_builtin_hash` connects this producer to the actual target hash of identical copied calldata; its per-input concrete Fixed equality remains explicit. Concrete-Fixed controls cover both pipelines, wrong preimages, lower-horizon timeout and dangling references. No raw-local cleaning, collision freedom, placement or compiler adequacy follows from these laws.

`HeapWriteback.run_checked` handles arbitrary finite numeric-array write lists, deriving the valid prefix and first invalid index with the existing list traversal and the actual represented array length. It proves complete Source success/error, the prefix word/byte image, unchanged locals/other roots and every-initial-H MemOK. A halt retains the successful prefix and does not execute its suffix. This is local monadic execution, not an implicit transaction rollback or universal memory support.

`HeapWriteback.checked_reads` observes the actual returned state of an arbitrary finite numeric write sequence, whether it succeeds or halts at its first bounds failure. It derives agreement between fresh `readLoc`, every retained local alias expression at horizon `n + 2`, and the complete physical word bytes of the successful prefix. It preserves every initial MemOK; it does not resume execution after an error or infer rollback/intermediate-capture adequacy.

`ObjectWriteback.all_types_checked` computes the first actual `heapPut` type error for arbitrary lists of dependent Source object packets. Only the executed prefix requires the existing DataOK/Top/Inner invariants; unchanged heap typing makes the original type scan valid at every step. Complete success/error state, nonheap fields, unrelated roots and every initial MemOK are retained. Shared-child controls distinguish prefix preservation from suffix execution. This closes Source request sequencing, independently of physical decoder completeness.

`ObjectWriteback.putAll_perm` proves complete Source result/state equality for arbitrary permutations of type-correct dependent object requests to distinct root IDs. It derives pair commutation from actual heap writes and transports typing through the sequence. Same-root aliases and failing type guards are not covered by the order premise; controls show their observable order dependence. Data safety remains the existing separate Prepared/MemOK obligation, and physical serialization adequacy is not inferred.

`PhysicalObject.commit_many_checked` derives owner data invariants directly from concrete byte/string snapshot decoding, then proves complete Source batch success or first type error with exact prefix state and every initial MemOK. It reconstructs the complete raw snapshot without discarding residual bytes. Bytes/string and both-pipeline controls show the first decoded payload surviving a mismatch while the suffix remains unexecuted. This does not infer physical bounds or allocation ownership from decoding.

## Raw local words and physical bytes

`Adapters.RawPhysical` consumes the existing H11 `RawFrame` and bounded P6 byte operations. A store serializes all 256 raw bits; a physical byte-view load records them through the actual raw overlay write. Clean Source locals, world and unrelated raw cells remain separate. The roundtrip is raw-view equality, not administrative identity: a previously absent overlay becomes `some word`. Bool/u8 conversion occurs only at the existing explicit per-pipeline return boundary. Controls distinguish dirty words2/257 from their return values, preserve nonzero exterior bytes and roundtrip the maximum word. These are byte-view transport laws, not emitted MLOAD, dirty storage transport, allocation or universal pipeline adequacy.

The raw-local store now has an actual target instruction link: `RawPhysical.store_target` proves the published `Environment.cryptoStep` MSTORE result, including complete reached bytes and caller stack tail. `source_backend_wordBytes` derives equality of the existing Source/backend encoders; its helper handles arbitrary byte widths without a new encoder definition. Controls discriminate operand order and endianness. This strengthens the store side only: total byte-view reads are still not physical MLOAD steps, and gas/allocation/compiler adequacy remains separate.

`RawPhysical.load_frame` consumes the existing regional P6 WordFrame to derive a nonwrapping bounded byte span, an actual fixed-cell Evm word-machine load, and identical H11 raw-local readback with unchanged clean locals/world. Word indices are explicitly scaled by32, and the regional byte relation survives. Controls distinguish cell1/byte32 from byte1. The optional Bridge already provides external memory macro refinement (`ExternalEvm.MemoryRefinement.load_refines`) under its own Represents, preallocated-capacity and PaddingCorrect premises; those remain separate, rather than being inferred from this core theorem.

## Computed ordinary placement

`Views.ComputedPlacement.prepare` derives existing Placement objects from actual finite Source heaps. It inspects ordinary memory constructors, reports all unsupported occupied IDs, preserves sparse holes, and checks the computed final extent against Word range. Cumulative addresses use actual shape sizes; zero footprints retain size0 and reserve one byte solely for distinct addresses in this witness. It imposes no alignment rule. `Adapters.ComputedFrameHeap.prepare` then computes the canonical object inventory and physical frame, retaining separate placement, frame-room and object-image errors. Its roundtrip theorem proves whole Source identity without supplied coordinates, shape laws, separation or inventory.

The constructor selects a mathematical witness; it is not the Solidity allocator policy, target-chosen placement, retained allocation history, reachability or AllocationRefines. Preparation errors are not source/Yul failures. Existing canonical type support and owner MemOK, actual extent checks and frame bounds remain explicit. Controls cover sparse and zero-footprint objects, empty heaps, scalar-object rejection, huge extent overflow, and two actual Source allocations with complete physical/source roundtrip and residual bytes. The existing oversized-MemOK counterexample and whole memory contracts remain unchanged.

`ComputedFrameHeap.prepare_sound` derives complete Source/writeback soundness from an actual successful result, recovering its checked geometry and frame-room facts instead of asking consumers to restate them. `prepare_reserved` separately preserves real input ReservedOK; no reserved byte is initialized or cleaned. Controls distinguish frame-room and unsupported-child errors and confirm that an input zero-word7 remains7 when ReservedOK is absent. Those failures and bytes are preparation observations, not language admission or allocation decisions.

Successful computed image preparation also yields the original `ObjectWord`/`ObjectByte` read laws (`prepare_word` and `prepare_byte`) without extra MemOK or canonical-decoder support premises: the actual constructor result already supplies typed images, coverage and unique IDs. `prepare_residual` retains separated bytes, and `prepare_prefix` retains every scratch/reserved byte below128 even without ReservedOK. Kernel controls observe headers/payload bytes and retain an invalid zero-word byte7. These are conditional read-side laws; the universal `MemoryLayoutObligations.realize` contract remains open.

`ComputedPlacement.allocRef_geometry` transports the computed witness through actual Source allocation: every occupied old address and shape stays fixed, the fresh logical ID receives the old computed end, and the end advances by the actual shape reservation. Actual allocRef execution and every original-H MemOK follow from existing typed data validity. Zero-size spacing remains this mathematical witness choice; the checked Word extent is a preparation bound, not a language limit or target allocation policy. Target allocator provenance/refinement remains open. Controls retain two real aliases and include a zero-size allocation followed by a nonempty allocation.

`AllocatedComputedFrame.allocation_roundtrip` connects actual allocRef execution to complete computed-frame preparation and whole-source unchanged writeback for that same allocated state. Enlarged-heap codec support is derived from real old/fresh lookups rather than supplied as an output inventory. Initial every-H MemOK, typed object validity, canonical support, computed Word extent and frame capacity remain explicit. Controls preserve a nonzero unrelated tail in both pipelines. The supplied raw free word is not asserted to satisfy ReservedOK; this component neither initializes allocator bytes nor proves target allocation refinement.

`ComputedAllocationWrite.prepare` derives the new-object base, next free word, freshness and extent for the existing incremental typed encoder from a successful computed placement. It writes the new image and FMP rather than reconstructing old objects. Soundness derives whole-map reconstruction and whole allocated-source unchanged writeback from actual old image reads, owner MemOK, DataOK/Inner and canonical codec support. Residual bytes outside the new footprint and FMP remain exact; ReservedOK is transported only from real initial ReservedOK. Two-allocation controls retain dirty padding99 and unknown tail170, with actual source byte/string reads and free words192/256. This does not transport dirty owned payloads or establish a target allocator policy/refinement.

`MemoryImage.point_congr` and `MemoryImage.disjoint_commute` cover every existing intrinsic image constructor, including pointer-valued word images, and compare complete raw maps under real span separation. `objectAllocationView_mstore_commute` includes the actual FMP update and preserves preparation None via Option.map. `heapPut_objectAllocRef_commute` compares complete actual Source results and returned references for any memory object, provided the write targets a genuinely old typed cell. It asserts neither MemOK from typing alone nor compiler/allocator adequacy. Controls distinguish mixed array/string disjoint writes, overlapping order, residual gaps/tails, and missing-target failure prefixes.

`MixedHeapOrder` proves full raw-map invariance under arbitrary permutations of distinct actual root entries, deriving physical separation from Placement and image bounds. Repeated complete encoding is idempotent and all bytes at or beyond the actual free extent remain residual. `generated_permuted_writeback` derives actual whole-source unchanged writeback for any permutation of the computed complete inventory from original owner MemOK and the existing canonical type profile. It does not assert that different same-root updates commute or replace changing-source transport. Six-root controls include shared child pointers, reverse order, gap/tail preservation and missing-root discrimination.

`InventoryDecodeOrder` preserves exact all-or-none preparation and the decoded typed-update permutation when root visit order changes while pointer candidates stay fixed. Distinct actual root IDs and original heap-type agreement then give complete actual Source result equality. The existing writeback entrypoint agrees with the alternate actual sequential traversal, including placement, retained history and candidate refresh after every write. These laws do not reorder candidate lookup, claim arbitrary wrong-typing error commutation, or reinterpret unsupported preparation as execution. Controls reverse a changed six-root snapshot with nonempty alias locals and separate invalid-bool preparation from an actual late source error prefix.

`InventoryCandidateOrder` removes the fixed-candidate restriction for actual candidate permutations. Placement uniqueness forces every matching owned pointer word to return the same logical ID, even with repeated candidate entries. The proof is lifted through the existing canonical member/object/update decoders, so the actual writeback entrypoint and sequential implementation may permute both candidates and distinct-root visits with exact Option/Source results. It does not add missing ownership, accept interior pointers or assert commutation of different same-root updates. Changed six-root controls retain alias locals and include duplicate candidates, missing/interior/wrong-shape pointers and dirty-bool preparation failure.

`InventoryReplay.inventoryStateWriteback_replay` constructs output codec support from actual heap-type preservation, recovers exact image reads from the constructed raw-map equality, and proves that the same snapshot replays as whole-source identity through any permutation of output entries. Its output realization keeps the original allocation history and preserves every original-H MemOK from the real initial invariant. Initial coverage, distinct roots and canonical type support remain explicit; no final inverse/view/support law is supplied. Controls cover changed and zero-length snapshots and distinguish retained capacity from incorrectly resetting the origin to a minimal current shape.

`SnapshotHashBinding.sourceMemoryHash_snapshot` derives actual post-writeback source keccak agreement with the SAME supplied raw snapshot. The constructed output inventory supplies exact payload bytes; caller locals remain the actual locals, and the expression result word matches physical keccak using the same Fixed field at horizon n+4. It retains every original-H MemOK conditionally and assumes no final byte/hash/view law or hash injectivity. Controls cover changed bytes through two incoming aliases, zero-horizon timeout and wrong header/padding input ranges. The source profile remains an actual bytes.memory local; target compiler and allocation correspondence remain separate.

`CalldataHashBinding` proves actual checked keccak evaluation for a bytes.calldata local, including the existing implicit conversion and real memory-object allocation. The returned source state retains that allocation. Physical payload hashing uses the effective clipped slice length, so oversized declared lengths are not replaced by zero-padded hash inputs. Both aliases, empty/past-end slices and timeouts are covered; every original-H MemOK follows from the actual allocation rule. This binds payload bytes only: header/FMP allocation refinement, target offset wrapping and ABI reachability remain separate.

`P6CalldataHash.source_target_clipped_hash` connects the actual calldata-local source expression, its implicit allocation, the published bounded P6 frame copy, and the published target KECCAK256 step over the same derived clipped payload. Source and target word agreement retains an explicit per-input Fixed-to-concrete-Keccak premise, discharged by the controls using Roadmap.Evm.withKeccak in both pipelines. Stack tail, copied memory, carrier/key and every original-H source invariant are retained. Empty copy/hash at maximum offset is covered. Full allocator/header/FMP, World-state, compiler and gas adequacy remain separate.

## Nominal inventory preparation

`Views.NominalInventory` adds declared memory arrays of UDVT elements to the
existing inventory dispatcher, reusing `NominalMemory.decodeArray`. Existing
canonical cases retain their decoder. Missing nominal metadata fails preparation
even for an empty array; successful updates retain the original allocation-size
check and execute `runInventoryUpdates` on the actual Source state.

`snapshot_encode` derives exact typed data from canonical element words.
`reencode_raw` reconstructs the complete supplied byte map for an arbitrary
successful mixed preparation sequence, and `writeback_MemOK` preserves every
initial owner typing. The controls inhabit an exact changed whole-source result
with two real aliases and the actual owner invariant. Canonical failure remains
preparation `None`, not source refusal or cleaning.

`NominalInventoryUnchanged` derives unchanged typed data from actual image
reads and derives update capacity from retained placement. Its encoded-view
law preserves the complete source state, including administration. Repeated
visits need no distinct-root premise; constructing encoded reads still does.

`NominalInventoryPreparation` proves completeness of the existing heap-image
preparer for this explicit profile using actual owner `MemOK`. The existing
finite enumerator then derives coverage and unique IDs. `generated_roundtrip`
requires no supplied complete inventory or inverse law. The mixed-heap control
inhabits this result with nominal aliases, an unrelated byte object and nonzero
residual bytes.

Valid placement, retained history and the canonical/declaration profile remain
real premises. `NominalInventoryView` connects successful changed snapshots to the existing
inventory realizer. It constructs retained output placement/history and proves
exact complete Source output, refreshed coverage, preserved heap metadata and
full raw-map reencoding. Its generated variant derives initial coverage from
owner preparation. A kernel control ties this output view to the actual changed
nominal source state and its owner invariant.

`NominalInventoryTransport` derives decoder refresh through the actual finite
write realization, including failed canonical preparations. Its prefix law
pairs each actual finite source-write prefix with fresh decoder transport.
No member-agreement law is assumed at that public boundary.

`NominalInventoryReplay` derives output support from preserved heap types and
raw reads from the constructed view. Replaying the same snapshot in any output
permutation preserves the complete resulting source state and original retained
history. Controls establish an actual changed state, a nonempty prepared prefix,
and a reverse replay containing two distinct roots. The mixed reverse fixture
uses an unchanged input; it is separate from the changed singleton fixture.

`NominalInventoryDynamic` proves exact singleton compatibility with the existing
retained-array operation, including `None`, source errors and whole-state
results. Controls transfer real source shrink-to-zero and regrowth to the
inventory API, construct the regrown shape/history/raw view and preserve every
original owner typing. Canonical data that fits a free-pointer gap still fails
preparation when it exceeds the original owned allocation. This is not a Yul
refusal or a new capacity policy.

`InventoryTraversal.inventoryStep` factors the existing typed planning step:
decode, original-capacity check, actual heap write, placement/history and candidate
refresh. The canonical traversal retains its signature and structural equations.
`NominalInventorySequential` uses that same step and proves exact snapshot and
complete Source-result agreement, including `None` and repeated roots. No decoder
agreement premise is supplied at the public entry point. Controls cover a generated
mixed inventory, retained regrowth, duplicate visits, an invalid first scalar and
a later capacity failure after a changed nominal prefix. Byte length 4 fits the
existing rounded payload; length 33 exceeds it although canonical decoding succeeds.
The initial mistaken length-4 negative expectation is retained in raw evidence.
Legacy frozen behavior and exact cons-equation checks pass; the existing mixed
control check measured 22 seconds before and 21 after in the same serial runtime.

`InventorySnapshotCursor` pairs physical evidence with the actual Source state.
Each successful step executes `runInventoryUpdates`, derives its new placement,
images and original retained history from `realizeInventory_run`, and projects
exactly to the existing writeback API. Completeness is a preserved initial
coverage property, not a cursor field. Every initial owner typing, heap types/next,
entry IDs, placement/free choice and whole administrative state are preserved.
Each successful snapshot reconstructs its entire supplied byte map, including
residual bytes. This does not claim that selected entries cover missing objects.

`InventorySnapshotHistory.runSnapshots` processes arbitrary finite changing input
snapshots. Unsupported preparation stops before executing any write from that
snapshot and returns the exact prior Source state/cursor and unexecuted suffix.
Append/resume and suffix laws preserve chronology; completion of a nonempty input
list reconstructs the last raw map. Controls include retained zero/regrowth,
negative values, both aliases, mixed nominal/bytes roots, partial-snapshot and
suffix-execution discriminators, duplicate visits, original-capacity loss and
nonzero tails. Safety for the inhabited fixture is proved for every input list;
factoring avoids concrete byte-function normalization under unchanged limits.

`PhysicalSnapshotSlice` obtains final bytes from the actual published
`Backend.Environment.runSlice` and passes them to the same Source snapshot step.
It retains the complete reached stack/memory on both preparation outcomes.
Outer `None` remains the partial target evaluator result; `some (reached, none)`
retains real physical output with unsupported canonical preparation. Neither is
promoted to an invented Yul refusal or rollback policy. Target concatenation is
proved before the single final synchronization, so an actual later store may
repair dirty intermediate bytes. The existing backend writer and `Views.mstore`
are proved equal on the entire mathematical byte map. A kernel witness connects
actual generated PUSH/PUSH/MSTORE to actual Source shrink; executable controls
cover repaired/final dirty signed words, retained header changes, stack tails,
MSTORE8 into a byte-object sibling, residual bytes and wrong destinations.

`SelectedPhysicalStore` consumes the published `Compilation.PhysicalStore`
selector and instruction generator with the existing materializer/checker proofs.
The selected nonwrapping word program is32MSTORE8 stores (96instructions), not
one native MSTORE. Its final bytes feed the actual Source snapshot API, retaining
unsupported canonical preparation separately from target execution. For byte
writes outside every actual image span, initial complete encoding, pointer
coverage, distinct IDs and the existing decoder profile derive whole-Source
identity while the raw complement changes. The kernel controls instantiate a
selected header shrink and a nonzero residual write. Further controls show the
exact last valid word boundary, dirty final target bytes, and a reserved FMP
corruption despite unchanged Source data. Outside-image separation alone is not
reserved-memory safety, allocation adequacy or language admission.

`CheckedResidualStore` consumes the existing `prepareResidualWindow p destination 1`
result. Its actual inventory and checked geometry derive byte exclusion and
reserved separation. Initial `ReservedOK` concerns the residual carrier;
encoding and the compiled byte update derive validity of both reserved words on
the complete map. The output reconstructs the changed raw complement while
preserving the entire Source state and every initial heap typing. No planner or
admission predicate is added. A kernel witness uses the actual computed nominal
and byte-object inventory. Controls preserve byte254 in current padding, then
run actual header growth: Source reads that retained fourth byte and a new plan
rejects its now-live location. Reserved/owned preparation rejection stays separate
from the actual target byte instruction's ability to execute. Current checked
padding does not establish future ownership, allocator provenance or gas bounds.

`P6ResidualCopy` connects the actual `P6ByteMemory.copySnapshot` operation to
existing computed residual-copy requests. Genuine initial frame/image agreement,
separate source/destination capacity room and the request's existing Word-range
facts derive the full updated image and actual Source identity. Copies read the
old complete physical snapshot, including owned source payloads. Reserved words
are preserved by the checked destination. Capacity and reached high-water
accounting remain distinct; the output uses its own `Fits` fact. Controls build
the input frame from the computed nominal/byte heap, copy owned byte 7 into
residual byte 300 (whose residual-only source would be 165), and raise the actual
high-water field from 8 to 10 words. Both overlap directions and exact empty-copy
frame identity at maximum Word offsets are checked. Frame carrier state/key
remain separate from logical Source state. No MCOPY opcode, allocator, gas or
whole-program theorem is supplied.

`P6ResidualSequence` executes arbitrary finite lists of those existing requests.
Each step transports the remaining capacity premises through actual capacity
identity and reads the newly reached frame. Full images agree with chronological
`residualCopies`; actual Source writeback and reserved validity hold at every
input prefix. Prefix length selects input rather than imposing a resource cap.
Carrier state/key/capacity persist, while output `Fits` uses reached accounting.
Controls copy owned bytes to 300 and then from 300 to 310, distinguishing fresh source
bytes from zeros in the initial frame. Reversed order differs, and interspersed
maximum-offset empty requests preserve earlier payload/accounting. These are
boundary writeback laws, not instrumentation of arbitrary Source computations
or a native MCOPY/compiler/allocator theorem.

`P6ResidualCapacity.checkedCopies` computes those capacity premises instead of
requiring a caller proof for the whole request list. It retains the actual
successful frame prefix and exact pending suffix at the first unready request.
The accepted prefix and its room proofs are constructed, then identified with
`runCopies`; its full view, Source identity, reserved validity and carrier facts
follow. The pending head is proved unready against reached capacity. Controls
separate source/destination failures and discriminate lost prefixes, clipped
copies and skipped failures; empty maximum-offset copies remain valid. Capacity
failure denotes unsupported bounded-frame preparation, not a Source/Yul halt,
native EVM failure or allocation verdict.

`P6ResidualResume` uses the producer's existing `expandZero` and resumes only
`checkedCopies`' pending suffix. The complete byte image, carried state/key and
high-water accounting are unchanged by reservation; capacity grows by a word
multiple. The two actual executed prefixes construct one chronological residual
image and unchanged whole Source writeback. Insufficient reservation can still
leave requests pending. Controls cross capacity512 into544, then copy from the
newly written tail; access raises high-water to17. Replaying the accepted
overlapping prefix changes byte232 from8 to7, unlike correct resumption. This is
bounded representation preparation, not allocator reachability or EVM expansion.

`P6ResidualReserve` computes the maximum source/destination end of nonempty
pending copies and the least sufficient number of extra32byte words. Empty
maximum-offset requests contribute zero. The resulting reservation derives all
capacity premises, proves actual checked completion and reconstructs the full
chronological residual map with unchanged whole Source writeback. No output
coverage or completion witness is supplied by a caller. The existing Word-range,
layout/canonical-codec and initial whole-image premises remain explicit. This
closes this bounded preparation's capacity obligation, not runtime allocation,
resource feasibility or general Source/compiler correspondence.

`P6SnapshotCopy` connects the actual bounded P6 copy to `snapshotStep`, allowing
owned destinations as well as residual regions. Both preparation outcomes retain
the complete reached frame. Successful preparation derives actual Source writes,
complete-map reencoding, administrative preservation, inventory coverage/IDs and
every initial owner `MemOK`. Arbitrary copy spans do not imply reserved-word or
memory-safe permissions. Controls copy an owned nominal signed field and observe
both aliases while preserving a sibling byte object and nonzero tail; a copied
noncanonical word retains its physical output with preparation `None`. A separate
kernel self-copy witness derives preparation using existing codecs. Changed-field
preparation existence is an executable control here, not an independent kernel
existence theorem. No intermediate observations or whole-program correspondence
are inferred from this final-boundary adapter.

`P6CopyPreparation` supplies the next constructive step: a full copied word
is proved equal to the old source word, and canonical nominal word facts derive
an actual inventory update with its exact dependent data. The real shape bound
remains explicit. A two-root explicit codec image constructs both the changed
nominal update and the untouched byte-object update, then proves complete
snapshot preparation exists in the kernel. The second owned word changes from
32767 to-1. `changed_source_view` derives an actual complete Source result,
whole-map reencoding, administrative preservation and every initial owner typing
without assuming successful preparation. This uses the explicit codec image;
it does not identify that image with all generated-image or arbitrary-copy
preparations, nor supply allocator or compiler correspondence.

`P6CopySource` identifies the real `Source.heapPut` action from prepared entry
identity and exact dependent decoded data. A sibling equal to its actual current
cell makes no administrative change. The concrete changed-copy proof runs both
actual actions and identifies the entire resulting Source state with a specified
`Heap.write`; it does not stop at an unspecified existential output. Kernel
`indexLoc`/`readLoc` checks show both aliases now read-1 at the changed index,
where the initial state read32767. The byte sibling remains its exact original
typed cell and every initial owner typing survives. This is the concrete two-root
copy result, not arbitrary Source-call or compiler adequacy.

`P6CopyHistory` runs finite lists of existing bounded source/destination spans,
transporting them through actual capacity identity. Each copy precedes canonical
synchronization; a successful result refreshes the actual Source state, retained
placement and inventory for the next copy. Every initial owner typing, whole
nonheap administration, inventory IDs and coverage survive successful prefixes.
Completed sequences reconstruct the entire reached map from the initial view.
On preparation `None`, Source retains its accepted prefix and the physically
reached failed frame is kept. The first pending request has ALREADY copied;
only the later suffix has not run. There is no blind pending-replay resume API.
Controls distinguish late failure from reversed order and show an overlapping
failed-copy replay changes byte129 from255 to0. This is synchronization of actual
component copies, not Source/Yul failure, rollback or arbitrary program adequacy.

`P6HistoryHash` connects completed copy histories to actual Source memory-byte
hashing and the KECCAK256 micro-step. It derives the shared payload from the
refreshed complete view, coverage and inventory IDs, retaining actual poststate
local/cell/span facts and same-input Fixed agreement explicitly. Initial view
and completion remain distinct premises. A separate live-frame theorem hashes
raw reached bytes even after unsupported preparation, with no Source-equivalence
claim. Controls bind nonempty byte payloads through two actual Source aliases
at an empty-history boundary and hash a failed nonempty history's retained
`[0,255]` input, distinguishing prior canonical `[255,255]` and wrong padding
ranges. Finite digest inequalities do not assert injectivity; the micro-step
does not establish gas or whole-frame memory-expansion accounting.

`P6HistoryHashRef` uses actual `Source.EM.sub` with a typed byte-reference local
and the real hash expression. Success returns child locals and restores the
entire caller state; the actual zero-horizon error restores caller locals too.
The query's current-view premise is derived from preceding synchronization in
`completed_hashAt`. A concrete nonempty owned-copy history reaches its exact
changed Source state, hashes the unchanged byte sibling `[7,0,255]`, and retains
the caller's changed nominal aliases. Kernel proofs construct the history result,
query view, Source evaluation and target KECCAK step; no successful preparation
or final-state law is an input. This does not claim that the hashed payload
changed, nor prove reference formation, escape capture or callInternal adequacy.

`P6ByteCopyPreparation` constructs canonical byte-object updates from actual
copy readback, header, payload and retained-capacity facts. The changed-payload
control copies two overlapping bytes from224 to225, deriving `[7,7,0]` from
`[7,0,255]` while retaining length3. Actual whole-inventory Source writes yield
an exact byte-root heap update; the nominal sibling, both caller aliases and
every original owner typing survive. The nonempty history constructs its
refreshed view and the real Source subcontext hash and KECCAK step consume the
changed payload. Nonzero padding remains unchanged. The concrete old/new digest
comparison is finite evidence, with no injectivity or compiler/gas claim.

`P6ByteObjectCopy.payload_copy` generalizes byte-payload transport beyond the
fixture. From an actual complete initial encoded heap, byte-root lookup and
valid equal-length spans, it requires the destination to be empty or contained
in that root's live payload. Header preservation and retained capacity are
derived from actual Placement/history; new bytes come from the real reached
frame. The actual Source action and existing inventory realization construct a
complete refreshed view, coverage/IDs, unchanged other cells, every initial
owner typing, heap type/next and address/free metadata. Source spans may read
any represented region, including overlap. Empty maximum-offset copies remain
no-access and preserve whole Source state. This is same-length payload support,
not growth, arbitrary owned writes, static-call or assembly admission, resource
feasibility or allocator/compiler adequacy.

`P6ByteFamilyCopy` factors that proof over the existing indexed
`heapByteType`/`heapByteData` APIs. Bytes and strings share a physical shape but
retain their actual Source constructors. The old `P6ByteObjectCopy` signatures
are unchanged byte specializations; there is one payload-copy realization proof.
The string witness uses the existing three-root Source heap and copies across a
word boundary from its last string byte and nonzero padding. Its resulting33byte
payload is `0x61` followed by32bytes of `0xa5`, retained as Source string data
without UTF-8 validation. Actual owner observation and heap-type distinction are
proved; both surrounding byte objects and the whole view survive. This extends
same-length payload support, not string indexing, growth or allocator adequacy.

`P6RetainedRegionCopy` extends selected byte/string copying to headers and
original retained regions. It keeps the reached frame on preparation `None`;
for this selected family only, failure is exactly overflow of the decoded
rounded footprint beyond original capacity. Whole-view success also requires
the destination to be empty or contained in the actual original region.
Current occupied roots, addresses and footprint bounds transport through real
retained lineage to derive original separation and protect other objects.
Actual Source writes, refreshed views, coverage/IDs, layout and typing facts
are constructed. The kernel two-step witness shrinks a33byte string to zero,
then uses that actual result's refreshed inventory/history to prepare regrowth
to64. Finite controls observe the original33bytes plus31nonzero padding bytes,
reject current32byte capacity as an origin, and retain a copied65header on
original-capacity failure. These are preparation outcomes, not language refusal,
deallocation, cleaning or allocator/call-rollback adequacy.

The slice adapter does not assume or establish initial Source/raw agreement,
resource/capacity correctness, intermediate observation/capture or compiler
correspondence. General physical execution beyond that published slice, arbitrary
frame/call/rollback adequacy, broader mixed and nested dynamic history, dirty-word
transport, universal ownership, allocator reachability and compiler adequacy
remain open.

The `P6ByteReferenceReads` adapter proves actual Source length/read/write laws
for both byte and string heap cells. Resolved memory-byte location formation
has no current-length guard; read and write operations check bounds and retain
the exact panic payload and whole state on failure. Successful byte writes
preserve the real heap constructor and surrounding Source administration.
The retained-region control obtains the two heaps from the existing sequential
shrink/regrowth preparation: index 40 fails at length zero and reads the raw
regrown payload at length 64. These synthetic heap/frame witnesses establish
neither allocation reachability nor a historical successful index-40 access.
General producer capture, arbitrary source/frame adequacy and the remaining
original work/backfill obligations remain open.

`P6ByteReferenceWrite` connects actual Source memory-byte writes to bounded
MSTORE8 updates of the existing frame. It derives the nonwrapping payload address
from the real placement and logical index; physical capacity remains a separate
premise. `mixed_entry` derives input header/payload facts from the actual covered,
duplicate-free mixed inventory. The write theorem proves exact typed writeback,
selected-object reencoding of the whole updated map, every-original-H MemOK,
and preservation of other heap cells and every exterior byte. It does not yet
construct a refreshed complete mixed inventory. The unchanged-byte law preserves
the whole Source state and byte map; frame access accounting remains distinct.
The three-object string control changes the final byte of a partially occupied
word, preserves nonzero padding, and distinguishes the numeric MSTORE8 operand
from a left-aligned Source bytes1 word. No general compiler, static-call,
allocator-provenance or dirty-local adequacy is claimed.

`P6ByteWriteInventory.write` closes the complete mixed-inventory refresh step for
these valid byte writes. Canonical preparation constructs the updated entry;
actual placement separation preserves the other images. One resulting inventory
supplies the actual Source write result, selected writeback, whole mixed-map
reencoding, complete coverage, IDs, resulting cell, unchanged coordinates and
every-original-H MemOK. Original retained-allocation history remains available
for the next operation. The two-write control feeds the first actual heap,
frame and history into the second and exports both source runs and full maps.
Missing-entry and stale-image controls distinguish coverage loss and accidentally
overwriting the changed byte. This does not discharge arbitrary producer/frame
adequacy, allocation provenance or the remaining original queues.

`P6ByteWriteSub` transports these writes through actual `Source.EM.sub` for
arbitrary typed child locals. One realized heap supplies child success, a later
explicit Source halt, restored caller locals and whole mixed-map reconstruction.
A late halt passes the updated store; this is not transaction/frame rollback.
Immediate out-of-bounds Source failure instead preserves the whole prior Source
state, without claiming a separately executed physical store was undone. The
empty-child control retains two suspended caller aliases, and both actual owner
reads observe the changed string. Caller MemOK is transported from its own
invariant; arbitrary child-local safety and general call instrumentation remain
separate obligations.

`P6ByteAssignment` connects the existing resolved Source assignment expression
with local reference, index and bytes1 operands to the physical byte-write
inventory. It proves the actual RHS-first evaluation, location formation,
RVal conversion, write and returned value at horizon n+3. Bounds panic and a
horizon-1 timeout are distinct Source results; neither claims to undo an
independently executed physical store. Concrete typed contexts and globals
inhabit controls for both Source pipeline selections. This local-operand result
does not cover arbitrary effectful assignment operands or recursive producer
capture. The returned bytes1 word keeps its genuine left alignment.

`P6ChainedByteAssignment` covers an actual effectful RHS: one resolved byte
assignment nested inside another. At horizon n+4 the inner write completes
before outer location formation. The universal laws impose no distinct-index
premise. Physical composition constructs two actual refreshed inventories and
exports the nested Source result, both complete maps, coverage/IDs, sibling
preservation and every-original-H MemOK. Original allocation history feeds the
second update. Controls cross indices31/32 of the same string and distinguish
an inner panic (no outer write) from an outer panic (successful inner prefix
retained). This concrete operand composition is not a general arbitrary-expression
producer theorem, and no independent physical write is erased on Source failure.

`RetainedLocalAlias` reuses the published actual Source local-assignment law to
prove capture for every intrinsic type and local index. Entry, final and returned
reference scopes are derived from that computation. Overwriting a local does
not erase its entry paths, and a later explicit halt retains both assignment
effects and captured references. The store stays exactly unchanged; every
original owner heap typing is preserved. Static path typing is derived separately
from actual MemOK. Controls overwrite dormant child1 with child0 while outer
length is zero: final-only collection loses child1, whereas captured duplicate-safe
visits retain both. This establishes the local-alias producer case, not global
producer completeness or realization of the newly enlarged captured inventory.

`RetainedLocalAliasImage` connects the actual alias producer's unchanged store
to the existing captured-image source traversal. Registration coverage is proved
for expanded snapshots. The two-dormant-child control computes the image from
captured indices `[1,0]`, checks eight real field coordinates and separation,
and derives canonical Source views, exact whole-storage unchanged writeback and
full raw-map reencoding. Newly observed child1 owns its low value99 while high
padding bits remain residual; the stale-complement and no-cleaning controls
make that distinction explicit. These are checked snapshot ownership facts,
not a logical write, journal transition or global retained-reference adequacy.

`RetainedAliasOwnership` composes actual local alias production and the checked
ownership plan's `Source.applyOp` in one Source computation. The plan is indexed
by the actual post-assignment state and capture scopes. Only source success
advances the complementary journal; static storage refusal retains the completed
alias prefix and old residual journal. Whole-map reconstruction, every-original-H
MemOK and other-account/bank journal isolation derive from that same result.
The two-child control grows child0 from2 to3, recovering tail77 while preserving
child1's99 and high padding bits. Paired rollback restores exactly the checked
post-alias external-state/residual boundary, not arbitrary caller locals or a
whole call. Canonical preparation failure and general capture/frame adequacy
remain separate obligations.

`RetainedAliasSequence` indexes the next checked plan by the exact first Source
state, residual journal and capture prefix. Its source projection is the actual
owner monadic bind. First refusal skips the second program; late static refusal
retains the first reached map and journal plus any second alias effect. Two
successes use the second completed map. Owner safety composes over both branches.
A ready-but-skipped control and a journal-reset negative distinguish these cases;
first/second requested headers are3/0. The checked preparation reproduction law
factors actual guard fields without omitting them or raising recursion/heartbeat
limits. The concrete factored control takes about45seconds; generic laws about2.
This explicit sequence does not establish general call/frame capture or rollback.

`RetainedAliasFrames` derives the child boundary from the actual first compound
execution, then connects the actual two-program result to paired external-state
and complementary-journal rollback. Child rollback preserves the completed parent
prefix; child commit followed by outer rollback restores the initial pair. Both
restore the corresponding complete raw map through the checked inventory. Controls
distinguish the prefix padding word from the initial residual packed tail. These
laws do not restore arbitrary caller locals, heap or logs and do not instrument
general call execution. Canonical preparation, capture completeness and general
source/frame adequacy remain explicit unfinished obligations.

`RetainedAliasTransaction` composes the actual two-program Source bind with
`EM.modSt` using `ExecState.endTx`; its complementary journal closes only after
that source success. Complete persistent reconstruction follows from the same
checked second plan. Transient state and both journals reset, while locals, heap,
logs, events and function locals survive the finalizer. Every original heap
typing remains safe on success and halt. A late-static control retains a genuinely
nonempty source undo prefix and the first complete map, so premature finalization
is rejected. This explicit success-finalization fragment is not `runTx`, transaction
admission, failure rollback or general source/call instrumentation.

`RetainedAliasSub` runs the checked two-program sequence inside actual `EM.sub`.
Its derived projection retains exactly the reached external state and residual
journal; caller locals return on success and halt. Full raw reencoding and paired
child rollback use this same result. Controls preserve the saved child1 caller
alias against a callee overwrite to child0 and preserve the first completed map
on late static refusal. Arbitrary caller-local safety, complete suspended-alias
capture and external-call admission do not follow from this local-context law.

`RetainedAliasSubSafety` closes caller memory safety for this concrete substituted
sequence. Each alias/storage program preserves the heap on success and static
refusal; sequencing and actual substitution preserve it too. Restored caller
locals then transport the caller's own `MemOK` at every original heap typing,
without a callee-local validity or empty-caller assumption. Controls derive the
restored dormant child's actual `RefOK`/`pathTy`, cover both static positions and
a differently sized caller context. This does not prove historical formation,
reachability, complete suspended-alias capture or arbitrary call adequacy.

`RetainedCallerCoverage` connects actual saved-caller capture to the finite visit
union and checked child packs. Every observed caller path accepted by the layout's
root/index selector has a corresponding prepared element; genuine caller `LocalsOK`
separately yields static path typing. No ancestor length or historical index event
is invented. The empty-locals halted-callee control computes both dormant packs,
actual source inventory, whole-store unchanged writeback and full raw reencoding.
The theorem establishes child-pack selection, not arbitrary descendant-path or
initial/escape reachability adequacy; successful checked preparation remains real.

`RetainedCallerHeaders` carries saved-caller-selected child packs into their
actual declaration-traced dynamic header registrations, then into the computed
source inventory. Header membership derives from the checked child packing;
no final membership law is supplied. The dormant child1 control uses the real
post-stamp cursor `102*32+2`, derives aligned slot103/offset0/width32, reads actual
Source length1 and rejects sibling slot101. This covers traced headers of selected
packs, not arbitrary descendant paths, reachability or full source adequacy.

`RetainedLiveCoverage` derives actual successful header-length reads and complete
membership of their generated live primitive registrations from source traversal.
The proof composes the existing header, child and image computations; callers do
not supply the final coverage law or length. Controls recover saved child1's
length1, packed payload slot2000 and actual value99, and reject static-roots-only
coverage. Actual element-index and declaration-entry facts factor dependent
unification under unchanged budgets. Arbitrary dormant descendants, noncanonical
representations and global alias/source adequacy remain outside this result.

`PackedCellUpdate` derives a complete canonical finite view after an actual typed
cell write and the existing bounded field patch. Pairwise logical/physical
separation preserves all other fields; owned-byte reasoning proves the entire
complement map unchanged. Complete reencoding therefore uses the original
complement. The actual persistent `Source.setCell` projection keeps bank and
nonstatic premises explicit. Controls write retained uint16 payload99 to42,
preserve high padding and neighboring88, and retain exact static refusal.
Unchanged writeback is identity on the already-written store, not the original
setter's administration. Changing ownership and dirty-owned adequacy remain open.

`TransientCellUpdate` reuses the finite packed-cell proof for actual transient
`Source.setCell`. It derives complete reencoding with the original complement,
persistent-world isolation, exact static refusal and paired rollback. Existing
endTx resets logical transient defaults, residual cells and both journals while
preserving persistent words; no zero-encoding law for arbitrary codecs is assumed.
Controls use the actual declared transient uint16 root after nontrivial source
prefixes, preserve padding and unknown slot99, read back7, preserve another account
and restore/reset through real frame operations. This admits no transient aggregate
or dirty-owned representation and proves no general transaction admission.

`MixedCellSequence` reconstructs both finite raw banks from one actual Source
bind of a persistent setter and a transient setter. Each uses its original
complement and real bank/separation/view premises. Exact first/late static
outcomes and paired rollback use those same operations. Static flags are explicit
per-operation frame inputs, not a proof that an executing frame changes mode.
Controls use both banks at slot0, read2/7 on success and2/old0xabcd on late refusal,
and observe persistent survival/transient reset at endTx. This is finite typed
operation composition, not general call, dirty-owned or changing-layout adequacy.

`RepeatedCellWrites` composes arbitrary finite lists of typed values through actual
`Source.setCell`, using one fixed frame and the declaration's computed bank. The
physical fold reuses the existing field patch. Its complete finite view and raw
reencoding retain the original complement; rollback uses the same chronological
Source operations. Owner Hoare laws preserve every original-H `MemOK` on success
and halt. Duplicate writes retain real undo entries, equal-value static writes
refuse, and empty traces remain pure. Controls cover both banks and nonzero
padding. This proves same represented-path composition, not changing ownership,
arbitrary path/program coverage or dirty-owned adequacy, and imposes no trace cap.

`FiniteCellWrites` generalizes same-path repetition to finite lists of existing
path-indexed registrations and intrinsic values. One fixed-frame Source program
selects each bank from real declaration metadata. Registered physical-domain
membership and initial separated views derive both final raw-bank reconstructions
with original complements. Owner safety, static refusal and paired rollback use
the actual operation list. Controls interleave packed neighbors, banks and a
repeated path; reversing the trace changes the result. A request omitted from the
physical registry still executes in Source, so registry evidence is not admission.
These fixed-registry laws do not prove full live-layout or changing-ownership,
dirty-representation or arbitrary Source/Yul program adequacy.

`DeclarationDefaults` proves zero encoding for available actual Source defaults
of declaration-selected codecs, then carries that law through offset relocation,
typed path registration and `packDeclarationPaths`. For computed registrations,
the existing zero-default check therefore tests only actual default availability.
No law is imposed on arbitrary user-supplied codecs. Mixed declaration controls
use the real packed metadata; the actual ordinary transient uint16 root resets
all raw slots using derived zero witnesses. Function codecs remain selected while
`Source.Val.default` at function type returns `none`; that owner boundary is not
converted to zero, a source refusal or a new language exclusion. This is not full
transient aggregate, dirty representation or source/compiler adequacy.

`FixedDeclarationDefaults` transports the selected-codec default law through the
existing aligned rows, fixed arrays, structs and ordered root packer. The checked
root interface uses the certificate's actual packing result. Available defaults
derive empty Source views, whole-store unchanged writeback and full zero-map
encoding. Controls cover Inner[2][2] followed by uint128[3] and mixed ordered roots;
absent cells and explicitly written defaults retain their distinct complete stores.
This proof recursion adds no planner or depth cap and does not admit transient
aggregates or synthesize unavailable function defaults. Broader adequacy is open.

`CellWritesCalldataHash` binds finite actual Source setters to the actual calldata
keccak evaluator. The setter result supplies its unchanged local reference; the
successful builtin allocates exactly one clipped-payload object and preserves both
reconstructed storage banks. Same-Fixed physical copying/hash agreement covers
the payload, and owner safety holds at every original heap typing. Low hash
horizons retain the completed write prefix without allocation; static setter
failure stops before hashing. Controls combine mixed writes, two calldata aliases
and an oversized reference, distinguishing clipped3-byte and padded5-byte inputs.
This does not establish ABI-entry provenance, allocator header/FMP realization,
whole Source-statement fuel transport or Source/Yul/compiler adequacy.

`CellHashFinalization` transports the successful combined write/hash run's
persistent encoding through actual transaction finalization. Its general reset
law preserves persistent residual slots, resets transient residual slots, reads
actual source defaults and clears both journals. Controls also finalize a late
hash timeout: completed persistent writes survive while transient cells reset.
This is explicit carrier finalization, including the timeout example, not
automatic transaction error handling. The encoding law uses the original map
complement independently of the supplied residual journal; their initial
coupling is not derived here. Finalization is not frame rollback or a claim that arbitrary default codecs
encode zero; heap placement and general call/source adequacy remain open.

`LinkedCellHash.prepare` computes both selected-account complements from the
supplied complete maps and packed registries, preserving other accounts' cells.
After the actual combined typed-write/hash run, `reencode` reconstructs the whole
persistent map using the finalized journal's actual cells. Unknown nonzero slots
survive while transient residuals reset. Preparation is an explicit constructed
initialization boundary: retaining an existing undo list does not prove its
historical compatibility, automatic initialization, or rollback transport.
Original canonical views, separation and request-registration premises remain.

`CellHashFrames` derives external execution of a combined typed-write/hash run
from its actual chronological source operations. A child consumes the reached
caller state and retained calldata local. Frame rollback restores the full
external/residual carrier; committing that child then reverting its enclosing
frame restores the initial carrier. A genuine initial finite view and computed
complement give whole-map reconstruction from restored journal cells. Preparation
precedes frame entry; no rollback across initialization is asserted. Controls
reverse child writes (leaving 2 instead of caller 3) and perform two real heap
allocations. These laws do not restore the allocated heap, establish call
admission, or claim complete Source-state rollback.

`CellHashRollback` executes actual `Source.mark` and `Source.rollbackTo` around
the combined typed-write/hash computation. The exact successful run restores
external writes and leaves the original locals/logs while retaining the hash's
allocated heap object. This matches `rollbackTo`; `enterInstance` separately
restores a saved heap, which this adapter does not implement. The restored map
is reconstructed using computed residual cells. A late timeout bypasses the
subsequent rollback operation and preserves its completed write prefix, so the
adapter is not unconditional undo or automatic transaction failure handling.

`CellHashMemory` connects the actual combined write/hash allocation to the
computed incremental object encoder. Header, clipped payload and FMP form one
physical image; its raw-map reconstruction and unchanged whole Source writeback
are derived constructively. The actual observed hash reads that image's payload
with the same Fixed hash. Unowned bytes, including nonzero tail padding, remain
exact outside the header/payload and FMP. Controls distinguish this full image
from a payload-only copy. Initial image reads, supported old types, owner MemOK,
reserved memory and exact computed Word extent remain genuine premises. The
computed placement is not proved to be the target allocator's selection, nor
does this discharge general allocation refinement or retained-history extension.

`AllocationRefresh` prepares a fresh computed placement after actual allocation.
It agrees with incremental coordinates on occupied objects and the free pointer,
while intentionally allowing unused future coordinates to differ. Existing typed
image forwarding derives all refreshed reads, including pointer-valued members.
`resume` uses these derived reads for a second incremental encoding and proves
one actual two-allocation Source sequence, whole-map reconstruction, unchanged
whole-state writeback and owner safety. Controls retain two nonzero paddings and
an unknown tail, actual old/new source bytes, and the existing max-one stride
for a zero-footprint mathematical object. Initial canonical support, owner
validity, old reads and exact Word extents remain premises. Target allocator
selection and general retained-history/refinement remain open.

`AllocationSequence.Certified` is a proof-only relation over actual source data,
reached states and checked placements. Each step records only actual shape,
exact Word extent, Inner/DataOK and supported element types; later read/view
laws are derived by allocation refresh. `realize` constructs the full physical
continuation for any certified finite list, one actual `Source.allocRef` sequence,
whole-map reconstruction, unchanged whole-state writeback, owner safety and
reserved-memory transport. All returned values retain their intrinsic types and
have valid references in the final heap. There is no added length or fuel cap.
The relation is not a new Source admission predicate: controls include a real
dangling-child allocation that Source executes successfully despite absent owner
validity. A three-object control contains a pointer to the first allocated object;
empty input leaves the original state and residual bytes intact. General Source
producer coverage, allocator selection and retained-history refinement remain open.

`NewMemory` connects actual `Source.evalE` new-memory expressions to the physical
encoder. It retains the existing local-length evaluation, `2^64` Panic `0x41`,
`Source.newData` computation, allocation and timeout outcomes. Constructive
physical realization derives a full map and unchanged Source writeback from
actual owner validity, canonical support, initial image reads/reserved words and
exact geometric room. Controls include static-frame `new bytes` and `new bool[]`,
exact size panic, timeout, padding and unknown bytes. This is the local-length
producer adapter, not arbitrary operand instrumentation or target allocator
selection/refinement. No new execution limit or admission exclusion is added.

`NewMemoryOperand.decompose` removes the local-only restriction for the actual
new-memory length operand: the owner evaluator's complete result and state feed
amount conversion, the existing allocation guard and allocation. Success, panic
and halt transport preserve that exact prefix. Physical realization requires
real memory agreement and owner validity at the reached state, rather than
assuming original-state facts survive arbitrary effects. Controls distinguish
postincrement's old allocation length from its new local, preserve increment on
size panic, and retain a condition write before later timeout. This is contextual
execution transport, not arbitrary intermediate-reference capture or target
allocator refinement; all existing horizons and outcomes remain unchanged.

`AllocationPointer` identifies the physical word of a new allocation with its
actual logical Source reference using existing checked pointer decoding.
Coverage derives from old/new inventory preparation. The existing pointer-field
writeback equals the actual new-expression/getV/writeLoc sequence, preserving
writer errors and owner safety at every original heap typing. Controls use a
real fourth object (logical ID 3, physical word 288), pointer-array aliases, a
bounds panic retaining the allocation, and interior/wrong-type preparation None.
This does not prove a target sink-word store or full changed-memory reconstruction,
which remain separate physical-writeback obligations.

`ArrayWordStore` relates an actual raw `mstore` to a typed array-member write.
Existing old/new `MemoryElement` codecs and genuine old reads derive updated
member decoding; the complete writeback result equals actual `Source.writeLoc`.
Static and dynamic headers remain correct, and selected-array encoding with the
same complement reconstructs the complete patched ByteView. Controls connect
new-reference allocation (ID 3/address 288) to parent-word storage at 256, retain
new/sibling payloads and unknown bytes, and reject wrong logical-ID/byte-offset
preparations. This equality concerns the selected array plus complementary bytes;
refreshed whole-heap changed-image reconstruction and target opcode execution
remain separate obligations.

`ArrayWordHeap` extends one-word array stores to the complete generated heap.
The changed array's image uses the new codec word; real separation and typed
transport preserve every other object's reads. These derived reads establish
whole-map encoding identity, complete coverage and unchanged whole Source
writeback for the actual post-write state, together with owner safety and
reserved-word transport. Controls tie the same new-pointer consumer to its
four-object heap, distinguish parent word 128 from 288, and preserve an unknown
tail byte 99. Initial MemOK, supported types, complete old reads and actual
codecs remain premises. Final `retainInitial` begins at the resulting heap;
arbitrary earlier retained-lineage extension, shared-zero/interior/dirty-owned
representations and target opcode execution remain open.

`ArrayWordRetained` consumes the existing `retainSameShapeWrite` theorem to
extend an actual earlier allocation lineage through an array-member write.
Whole-map reconstruction and unchanged Source writeback retain the original
allocation argument and derived history, rather than resetting `retainInitial`.
Controls allocate two words, execute a typed shrink to one, then write the live
member: original capacity 96, current size 64, free pointer 224, dormant word 9
and unknown byte 170 remain exact. Live Source reads see 42, while the dormant
index still panics under the current length. Current-shape recomputation would
choose free pointer 192 and is distinguished explicitly. These helper executions
do not establish high-level program reachability, shared-zero/interior/dirty-owned
representations or target allocator refinement.

`StructWordStore` derives a field's updated `MemoryFields` encoding from actual
`DataList.setNth`, retaining its field-type checks. One raw `mstore` then decodes
to the complete actual struct `writeLoc` result through existing canonical
codecs. Selected-struct encoding with unchanged complementary bytes reconstructs
the patched map. Heterogeneous controls update a pointer, boolean and uint256,
preserve sibling aliases and padding, and distinguish a wrong-type Source write
from dirty-bool canonical preparation None.

`StructWordHeap` extends the field write to every post-write heap image using
the actual old inventory, codecs and separated placement. It derives complete
map reconstruction, unchanged whole administrative Source writeback, owner
MemOK for every original heap typing, and reserved-byte preservation. Six
heterogeneous objects witness the changed pointer, unchanged sibling alias,
other objects and nonzero padding. The result uses `retainInitial`; extension
through arbitrary prior allocation history, target opcode execution and general
dirty assembly transport remain open.

`StructWordRetained` transports an arbitrary existing `RetainedAllocation`
through the same-shape field write and derives complete map reconstruction and
whole Source writeback against its original allocation placement. The supplied
history is preserved, rather than replaced with `retainInitial`. Controls chain
an actual child-pointer update and boolean update, preserving the sibling alias,
other objects, caller locals, padding and the successful prefix on a later
wrong-type write. This extends allocation provenance for these writes, not
arbitrary shape-changing histories or general dirty/target execution transport.

`ByteElementStore` connects actual `writeLoc (.memByte …)` to a single existing
`saveByte` patch. Bytes and string objects retain their type and length. Payload
replacement and region separation derive every post-write image read, whole map
reconstruction, original-allocation-history writeback, every-H MemOK and reserved
preservation. Controls cover bytes/string aliases, invalid UTF-8 bytes without
cleaning, padding, a source/payload byte-32 crossing, exact Panic0x32 state
preservation, and static memory-write success. No string surface syntax,
shape-changing update, target opcode execution or general dirty representation
adequacy is inferred.

`ByteElementFrames` connects byte transport to actual `EM.sub` success/halt:
caller locals restore, and the resulting heap passes through. Whole Source
writeback and physical reconstruction refer to that same reached state and
original allocation history. The separate actual `mark`/`rollbackTo` theorem
retains heap writes, as the owner restores only external journal/log fields.
Controls retain a caller prefix and child byte mutation through a late halt,
nested empty child contexts and explicit rollback, with suspended caller aliases
and exact bounds failure. These facts do not specify general callInternal,
external-world effects or an automatic memory rollback policy.

`MemoryDelete` runs the actual owner `zeroVal` before transporting a deletion.
For array elements and struct fields it keeps the computed `Val.default` result
and canonical word encoding explicit; bytes/string elements use the concrete
zero byte. The resulting physical patch reconstructs the complete map and
writes back the whole Source state against the supplied original allocation
history. Controls cover scalar/byte deletion, universal integer defaults,
unchanged siblings/padding, timeout, type error and Panic0x32. A reference-field
deletion is separately observed to allocate and redirect the pointer; the scalar
adapter supplies no physical theorem for that allocating branch.

`ReferenceDelete` supplies the allocating bytes/string branch for a struct field
from a computed initial placement. Actual deletion first allocates the empty
default, then writes its new reference. Existing typed images are forwarded to
the allocated heap; the new pointer word and all post-write image reads derive
from the same incremental allocation map. Public results include exact checked
allocation preparation, old/new coordinates, free-pointer growth, complete map
reconstruction and whole Source writeback against the allocated snapshot.
Controls keep a sibling alias and old data/padding, and bind allocation before
a later field-type error to its own complete map and Source writeback. Previously
shrunk allocation-history extension, other allocating defaults and target
allocator/compiler correspondence remain open.

`ReferenceDeleteRetained` extends the actual supplied origin through empty
bytes/string allocation, then the actual struct-field reference deletion.
Earlier retained writes/capacities survive; the final writeback uses that
extended origin. It derives allocation preparation, old/new coordinates,
free pointer, forwarded codecs, complete map and whole Source writeback from
old typed images and explicit nonoverlapping, bounded new-object placement.
Controls shrink a dynamic array2->0, delete an unrelated reference, and recover
the dormant aliases through the existing checked retained-array writeback after
regrowth. Original capacity96 differs from the current32-byte view. This
regrowth is canonical preparation/writeback through actual heapPut, not a new
Solidity expression rule or target execution theorem.

`RetainedArrayHeader` extends checked regrowth to a complete refreshed heap.
Canonical element words come from the same raw map, including dormant regions;
old image reads plus placement separation establish every post-header image
read. Actual canonical preparation and `heapPut`, original-H MemOK, complete map
reconstruction, reserved preservation and unchanged whole Source writeback use
the original allocation history. Controls compose shrink, allocating reference
deletion and regrowth without assuming new reads or a final inverse. The
original-capacity failure remains preparation `None`, not a language refusal;
no source length-assignment syntax or target execution is added.

`RetainedByteHeader` computes the resized bytes/string payload directly from
the same raw input, then derives all heap-image reads after the header patch.
Actual retained writeback and `heapPut`, original-H MemOK, whole-map identity,
original-history whole Source writeback, coordinates/free and reserved bytes
follow under the real retained-capacity check. Controls compose zero-length
bytes/string views, bytes regrowth, then string regrowth33->64; second-step
reads come from the first complete map. Four aliases recover old bytes and
nonzero padding made live by growth, with an unrelated third object preserved.
Preparation `None` beyond original capacity remains distinct from a language
verdict. No resize syntax, cleaning or target execution policy is introduced.

`ByteWriteSequence` executes every byte-write request through actual
`Source.writeLoc`. Its physical companion patches only on source success and
stops on the exact first error. Source projection holds for every input state;
for an actual bytes/string root, all finite plans derive complete reached-store
views, whole Source writeback and original allocation history, including late
bounds failures. Each successful step supplies the next step's reads. Controls
compose prior regrowth with repeated/cross-word writes, late Panic0x32 and a
skipped suffix, preserving aliases and caller locals in an empty child context.
This fixed-root adapter adds no evaluator, admission fragment, runtime cap,
automatic rollback or target execution theorem.

`MultiRootByteWrites` removes the fixed-root premise from finite byte plans.
Every request still calls actual `writeLoc`; lookup derives bytes/string
ownership or the owner's unchanged error, without per-request validity facts.
Whole reached-prefix reconstruction, Source writeback and original allocation
history cover arbitrary root/index sequences over the existing supported heap
profile. Controls alternate roots, overwrite a byte again, then stop on a
non-byte root; separate dangling/bounds cases preserve their prefixes. The
fixture's bytes/string locals retain their shared root0 alias. The physical
support profile remains an input representation condition, not Source admission.

`MultiRootByteFrames` derives whole nonheap Source administration and heap-type
preservation for finite multi-root byte plans. The actual callee run feeds
`EM.sub` and its physical companion; preserved heap typing restores validity of
arbitrary original caller locals. Whole caller Source writeback and complete
raw reconstruction hold on success and halt. Child locals need their real
incoming `LocalsOK`, without an empty/no-alias condition. Controls distinguish
caller aliases to root0 from nonempty child references to roots5/1. They retain
the same successful heap prefix on a late error; general call/rollback policies
and evaluator coverage remain separate obligations.

`BytePlanHash` composes actual multi-root writes with the existing checked
memory-keccak expression at evaluator horizon `n+4`. Preserved heap typing and
owner shape derive the final byte contents; the complete reached map derives
the exact physical preimage, using the same approved `G.fixed` hash. A write
error stops before hashing and retains its complete prefix state. Controls
cover repeated writes, caller-local restoration and stale/header/padded input
differences without hash injectivity. The initial typed bytes local/object
premises remain explicit; other hash producers and target opcode/resource
correspondence remain open.

The additive `sourceBytesOfMemory_alias_run` and
`sourceKeccakMemory_alias_run` laws also cover a bytes-typed local pointing to
an actual memory string object. `sourceStringBytes_pointer` proves the owner's
pointer-preserving conversion with the complete source state unchanged. These
laws retain invalid UTF-8 bytes and the actual lookup error; they do not prove
historical reference formation or surface admission. Existing bytes-only APIs
are unchanged.

`BytePlanHashAlias.transport` extends the write-plan result to string-backed
bytes aliases. It derives the reached object contents from actual type
preservation and heap shape, then obtains the physical preimage from the
complete map constructed by `MultiRootByteWrites.sound`. Its initial placement,
MemOK, supported inventory, old reads and reserved-region premises remain
explicit. The same source operation sequence and raw companion retain their
whole-map/writeback laws; no final contents or view are supplied by the caller.
Controls use two valid aliases to a string object, mutations across byte/string
roots, nonzero padding, a late non-byte write failure and restored caller locals.
They establish kernel source/view behavior, not target opcode execution,
external compiler observations or general expression/escape adequacy.


`BytePlanHashFrames.transport` carries that same child write/hash computation
through actual `Source.EM.sub`. Arbitrary valid caller locals are restored on
success and halt, while the real child heap effects remain. The typed hash
result and final child locals return on success. The theorem also derives
caller MemOK for arbitrary original H, complete reached-map reconstruction,
retained allocation history and unchanged whole Source writeback. Child locals
need their actual incoming `LocalsOK`; neither locals context must be empty.
Controls cover distinct caller/child aliases, a nested child with empty locals,
returned hash, exact late error and a later revert retaining the source heap
prefix. This is substitution transport, not general `callInternal`/`callAddr`
coverage, automatic heap rollback, transaction adequacy or target execution.


`MultiRootByteBoundary.above_free` proves that actual multi-root byte plans
leave every raw byte at or above the actual placement end unchanged, including
halted prefixes. Successful offsets are derived from the selected heap object's
layout and live index; invalid operations do not patch raw memory. This result
needs no initial raw-view or MemOK premise.

`P6MultiRootByte` uses that boundary to derive the final finite-frame `Fits`
condition from the initial frame and placement room, then constructs the exact
P6 frame for the coupled source result. Its `sound` theorem retains frame
metadata, original-H MemOK, complete reencoding, allocation history and unchanged
whole Source writeback. Initial owner validity, supported inventory, byte reads
and reserved words stay explicit; final Fits/view agreement is derived. Controls
cover six objects, both pipelines, repeated byte/string writes, a late source
failure, nonzero padding and the finite 2047/2048 boundary. A nonzero write beyond
the represented high-water mark fails Fits. This constructs a physical image;
it proves neither target opcode execution, memory expansion nor reachable
allocation refinement.


`MultiRootByteAppend.coupled_append` proves exact chronological plan
concatenation: a source error stops both source and raw updates, while success
feeds the reached pair into the suffix. `P6MultiRootByteRefresh.refresh` derives
the next plan's retained placement, owner safety, supported inventory, reads,
reserved words and finite-frame room from the actual first frame. No second-view
or second-bound premise is required for this construction. `append_success`
uses the derived placement addresses and actual first success to identify two
physical runs with the concatenated coupled execution. Readiness after an error
is not permission to execute its suffix. Controls prove this composition for
both pipelines and arbitrary original H, and distinguish stale Source reuse
from the reached state. General call rollback, opcode execution and allocation
refinement remain separate obligations.


`RawPhysicalInventory` constructs a complete physical snapshot from VY1's
existing `allWordCells` enumeration. Coordinates `base + 32 * cell.slot` use the
published cell/slot bijection; separation and full coverage are derived,
including both external-function fields. This is a constructed layout, not
compiler provenance. All 256 raw bits survive encoding and capture; the clean
Source locals/world remain unchanged. Capture records `Some` overlays, so view
roundtrip must not be confused with whole RawFrame administrative identity.
Every complementary byte is retained, including for an empty inventory.
Finite-frame Fits follows from initial frame room; Word-address nonwrapping
and emitted memory operations remain separate obligations.

`RawPhysicalProducer.transport` consumes the actual published P16
`RawSourceAdapter.Adapter.correct` field at its exact statement/context/control
indices. It preserves the reached Source representation through the physical
snapshot at every fuel, keeping the producer's coherent-input premise. It
neither invents an arbitrary producer nor establishes general dirty-local
Solidity readback. Controls cover four raw cells, dirty bool/u8 words, wide
external-function fields, nonaligned coordinates, padding, empty inventory and
absent overlays. Explicit existing return boundaries perform the bool/u8
readback. A real skip producer witnesses success/timeout transport; dirty
physical states remain incoherent, rather than being silently cleaned.


`RawPhysicalWriteback.unchanged` strengthens the raw-local view result to
identity of the whole encoded byte map after decode/reencode. Read facts are
derived from the actual complete encoder; no final coverage/inverse/view law is
supplied. `frame_unchanged` retains the entire finite P6 frame, including metadata
and all padding, using only the original room bound. This still does not equate
RawFrame administrative overlays: capture may install `Some` where none existed.
Controls demonstrate equal decoded raw views with different residual bytes,
reject reencoding from a zero residual, and retain dirty bool/u8 words. The
identity is physical unchanged writeback, not arbitrary dirty Source readback,
compiler layout provenance or target execution adequacy.


`RawPhysicalUpdate` connects actual `RawFrame.write` with a word patch of a
complete encoded inventory. Initial encoder reads and derived cell separation
supply all updated reads, full-map reencoding and decoded raw-view agreement.
Its `store` theorem uses the actual P6 store and published MSTORE slice, retaining
the complete new image and logical carrier/invocation key. An actual WordSpan
and agreement with the constructed cell coordinate remain explicit; there is
no inferred compiler layout or general gas/expansion theorem. Controls store a
full-width word in a uint8 cell, retain the bool and both function fields,
preserve padding, reject wrong coordinates and retain latest repeated writes.
Clean Source locals/world and explicit dirty-readback boundaries are unchanged.


`RawPhysicalInterior` handles one actual byte inside any represented raw-local
word. Existing exact big-endian codec inverses reconstruct all 32 bytes, so
updated inventory reads, complete reencoding and decoded raw-view agreement are
derived without canonical narrowing. Its P6/MSTORE8 theorem retains the real
Word offset, finite byte fit and coordinate agreement; only the MSTORE8 input
is truncated to one byte. Controls distinguish high/low byte order, retain the
other 31 bytes and sibling cells/padding, and reject byte32. Clean Source fields
and dirty readback policy remain unchanged. The compatible writeback helper
now reuses the existing byte-memory write/read identity proof.


`RawPhysicalAnyImage.encode_decode` extends the raw-cell roundtrip to every
byte map: decode all cells and reencode over that same map yields the identical
whole map, without an initial canonical/encoded-image premise. Exact 32-byte
codecs supply the inverse for each published raw Word cell. This is not a
canonical Source-value decoder or a dirty-storage policy, and capture still
populates overlays beside unchanged clean locals/world.

`copy_transport` applies this result to any actual bounded P6 snapshot copy,
including overlap and spans crossing cell boundaries. The reached inventory
room is derived from actual copy high-water monotonicity; complete reached-frame
identity and metadata are preserved by subsequent writeback. Empty spans retain
the published zero-length behavior. Controls copy 33 bytes from offset 33 to 34 across the
bool/u8 boundary, retain exact resulting raw words and padding, and distinguish
snapshot reads from overwritten-source chronology. Native MCOPY/compiler,
allocation and general dirty Source readback adequacy remain separate.


`RawPhysicalCalldata` binds actual `Source.Fr.cd` copying to the complete raw
word inventory. Reached frame room follows the existing byte-write accounting,
so arbitrary copied bytes and their right-zero-padding admit exact whole-frame
writeback without an initial encoded-image premise. A selected raw cell reads
the same 32 bytes as `Source.cdWordAt`; the actual typed `Source.readLoc` retains
its complete decoder result/error and unchanged Source state. Raw representation
is therefore distinct from typed acceptance, not a cleaning policy. Controls
keep raw word 2 while bool calldata reading reverts and uint8 accepts 2, preserve
static-frame Source carriers, right padding, maximum-offset zeros and exterior
bytes. Source offsets remain mathematical Nat after the initial Word; no wrap
or invented source-end bound is introduced. General dirty-local readback and
compiler CALLDATACOPY correspondence remain open.


`SourceEnvironmentSlice` connects the existing Source magic sequence to actual
`Backend.Environment.runSlice` execution of TIMESTAMP, CALLER and CALLVALUE in
that order, retaining the full Source state, target memory and stack suffix.
Actual Source values map to the resulting reversed stack order. BALANCE reads
use the existing code-presence/history Source balance projection and exact
bounded account conversion. Effectful operands select their actual post-state
and returned account; the adapter does not compile the operand or run a balance
read after operand failure. Controls retain distinct sender/self identities,
full-width value, history/code-selected balances, late timeout prefixes and
mismatched-ledger/order negatives. These are the existing gas-free local slices;
stack/gas/fuel resource correspondence, independent runtime-ledger agreement,
whole-world execution and compiler adequacy remain open.


`RawPhysicalHash` executes the published KECCAK256/PUSH256/MSTORE slice and
writes its full digest into a raw-local cell. The preimage is the original P6
snapshot, including when the destination overlaps that input. Existing raw-word
update laws derive complete reencoding/readback and preserved sibling/residual
bytes. `storeHash` records the input read through P6 `touch` as well as the
actual destination store; exact rounded extents and empty-input behavior remain
visible. Controls pin the old cross-cell preimage, output cell, target bytes,
stack tail, empty maximum-offset input and nonzero padding. A separate fixture
requires input-read accounting to grow from six words to eight while store-only
accounting stays at six. Preimage negatives assume no hash injectivity.
These are gas-free instruction-slice/physical-frame laws; Word-end nonwrapping,
resource adequacy, ordinary dirty Source readback and whole compiler/world
composition are not supplied.

`RawPhysicalReturndata.world_copy` connects the actual World target-memory
port to P6 `writeSpan`, using the actual strict returndata window to determine
both bytes and length. `transport` derives reached inventory room and complete
frame identity after refreshing all raw locals from that same reached map.
Physical capacity and Word-end nonwrapping remain separate from source-window
validity. Controls retain a dirty bool's interior byte, its sibling and nonzero
padding, and distinguish a valid empty window at the end from an invalid one
past the end. This covers raw local images; typed-heap adequacy, CALL execution,
resource accounting and source-level failure interpretation remain separate.

`RawPhysicalCallOutput` computes the physical write span from the actual
`callOutput` prefix. Its `copy` writes that prefix and touches the original
requested output span. Thus empty returndata retains all old bytes while a
nonempty requested span can still grow the physical high-water mark. `outside`
preserves the unwritten requested tail, and `transport` reconstructs the full
reached raw-local frame. `world_store` derives complete-map agreement with the
concrete World port. `call_copied` composes the actual World call adapter under
its explicit preflight, input-load, output-acceptance and invocation equations;
it does not provide a concrete call producer or invocation adequacy. Controls
separate short-return padding, retained dirty cells and requested-access extent.

`RawPhysicalCallFrame.execute_eq` retains the entire existing
`World.CompletedCall` carrier, rather than only its copied-memory projection.
Input loading is derived from the pre-call physical snapshot. Preflight,
Word-end nonwrapping, output acceptance and the actual invocation equation
remain explicit. Success retains the supplied operations and ordered trace;
callee revert restores the full caller journal entry and committed logs while
copying the revert-data prefix into caller memory. This does not imply an
enclosing-frame commit. Controls execute the adapter with a labelled synthetic
answer containing real typed Source journal operations: success changes storage,
revert preserves the prior caller value/log and physical output tail, and a
static value-bearing call is rejected. Concrete invocation adequacy is open.

`RawPhysicalCallAccess` records the input span as well as output access on the
reached P6 frame. Touching input changes extent only, preserving the complete
output image and World result. `execute_eq` still loads and invokes from the
pre-call snapshot; an overlapping output cannot supply a later input value.
The synthetic input-dependent control distinguishes those two snapshots.
An independent empty-output fixture keeps output-only extent at six words while
input access reaches eight. This is bounded physical accounting, not a claim
about gas ordering, concrete invocation adequacy or allocation refinement.

`HeapCallOutput.residual_unchanged` connects actual physical call-output/access
operations to the computed complete ordinary Source heap inventory. Canonical
owner preparation and unchanged object reads derive equality of the whole
administrative Source state on writeback; the reached residual bytes are kept.
Separation applies to the actual returned prefix, so an empty return may touch
a requested output span covering objects without writing them. Controls use the
existing six-object heap with shared children and preserve a nonzero unwritten
tail. Placement/history, owner `MemOK`, profile support and physical bounds stay
explicit. Object separation does not establish reserved-word safety, source
operation admission, allocation provenance or concrete invocation adequacy.

`HeapOutputReserved.preserve` protects the free-pointer and zero-word bytes
`[64,128)` from the actual returned prefix. Scratch bytes stay unrestricted;
`preserve_interval` includes empty returns independently of requested extent.
Controls start with genuine `ReservedOK` and show safe/empty outputs preserve
it without cleaning. A separate output writes byte `96` to `1`: the complete
six-object Source state still writes back unchanged, but `ReservedOK` fails.
Thus object-complement separation and Source identity do not imply reserved
safety, source admission or general shared-zero representation adequacy.

`SharedZeroRead` establishes limited read-side facts for empty dynamic arrays:
actual Source `lengthOf` returns zero, every actual `indexLoc` produces the exact
index panic without changing state, and `ReservedOK` supplies a zero header at
physical pointer `96`. Controls obtain two distinct logical IDs from two actual
`allocRef` calls. Their read observations agree with that header, but ordinary
`Placement` forbids either occupied object at `96`, and a raw-pointer-only
function cannot recover both identities. This does not select a new decoder or
prove target allocation, write-alias behavior, initialization reachability, or
whole shared-zero view/writeback adequacy. A corrupt-header control retains the
boundary between physical bytes and Source observations.

`SharedZeroLocalWriteback` preserves the identity already held by the actual
Source local. Preparation checks pointer `96` and its zero header, then returns
the retained typed value; `writeback` uses actual `writeLoc` and derives whole
Source-state identity. Read agreement additionally requires the actual local
binding and empty-object lookup. Controls preserve distinct IDs and a same-ID
alias, including static local assignment, and reject wrong pointers or headers
as preparation `None`. A forged-root control deliberately passes physical
checks, demonstrating that they validate neither reference provenance nor
emptiness. This is unchanged local writeback, not fresh pointer decoding,
shared object writes, allocation refinement or complete shared-zero adequacy.
