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
