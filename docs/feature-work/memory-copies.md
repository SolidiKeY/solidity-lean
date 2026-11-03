# Memory defaults and copies

`Solidity/Backend/MemoryCopies/**` holds partial certificate interfaces, local laws and inhabited controls for
G33 and G35.01/.04/.05/.06. It is not a frozen complete interface, and no
G33/G35 coverage is claimed. The existing intrinsic heap, storage-copy fold
and word allocator remain the only models; no second heap or evaluator is
introduced.

## Reused results

| Obligation | Reuse | Remaining work |
| --- | --- | --- |
| G33 | `Objects.DefaultBuilder`, `DefaultBuildResult`, `referenceArray_correct`, `ReferenceDefaults.compileDefault_correct`, `Objects.AllocatorRepr` | General nested/dynamic defaults; S03-PANIC41 size failure |
| G33 structs | `StructDefaults.source_pair_default`, `DefaultPlanSound` | Reused as is; their capacity premise is not a runtime panic |
| G35.01 | `copiedStruct_*` laws, `SVal`/`SFields`/`SVec.copyStToM` | Nonprimitive members, nested and dynamic aggregates |
| G35.04 | `MemoryOps.checkedSnapshotCopy`, `SnapshotSchedule`, `Heap.Keeps` | Alias versus deep-copy code and Source proofs (overlap laws `checkedSnapshotCopy_correct` exist) |
| G35.05 | `TypeGraph.Schema`, Source `zero*`/`load*` | Generic representation and traversal |
| G35.06 | `MemoryStorageCopy{Code,Compile,Laws,Source}`, `MemoryFixedMixedCopy` | Location/traversal certificates, mixed-location witnesses |

Source bytes and strings use `Source.STy`; `GraphTypeRel` has no bytes/string
constructors, and neither boundary may silently exclude approved shapes.

## Draft signatures

`Interface.lean` has the default builder certificate, storage-to-memory heap
and capacity-conditional word certificates, dynamic-length observations,
alias identity and overlap snapshots, and a finite heap traversal record that
claims no guarded-schema or total compiler coverage. The capacity-conditional
records are not yet non-vacuous: a `cost` with no room (for example `W`)
makes `StorageWordCertificate.correct` hold for empty code, as for the
existing `DefaultBuilder`. `cost` still has to be tied to the copied object's
allocation size.

`Premises.lean` has explicit boundary records with no assumed instances: the
S03-PANIC41 allocation failure and final Source state, G34 alias agreement,
and exact reached machine execution at location boundaries (G27.05,
G35.02/.03). They are not yet the producers' frozen APIs: the S03 size
predicate and the layout/path/location/refusal observations still need exact
statements.

## Interface V2: fitting allocator witnesses

`InterfaceV2.lean` (namespace `Solidity.Backend.MemoryCopies.V2`) replaces
the vacuous capacity condition. `DefaultCertificate` and
`StorageWordCertificate` each carry an `AllocatorWitness cost`: an actual
represented allocator input whose cursor fits the cost. `StorageWordCertificate`
also requires `0 < cost`. `InterfaceV2Laws.lean` derives `cost < W`, rules out
empty code (`code_ne_nil`), and refutes `cost := W` (`default_cost_W_impossible`,
`word_cost_W_impossible`). V1 stays for compatibility; consumers should use V2.
`SourceInterface.lean` holds the Source-side default, storage-load, copy and
outcome certificates at their existing qualified names. The finite intrinsic
`Interface.lean` no longer imports `Source.Hoare`; Source consumers import
`SourceInterface` explicitly.

V2 word correctness additionally fixes `base' g.val.id = cursor` and retains
every old `Objects.Gap` below the old cursor. These observations supplement the
allocator, address-map extension, machine shape and lower-cell frame.

`NewArrayLengthPanicPremise` contains length evaluation, successful index
conversion and the oversized-length condition only. The published `2^64`
length-panic equation is derived from those inputs in `SourceSize`, not
assumed as another premise. Finalize-allocation/cursor-overflow semantics
remain the separate S03-PANIC41 boundary.

`ControlsV2.lean` inhabits both V2 certificates using the existing empty-array
builder and a represented allocator. Its concrete execution observes root 40,
next cursor 41 and zero length, and preserves the reserved gap [0,8]. The
positive witnesses accompany the empty-code and cost-W negative controls.

`SourceControls.lean` inhabits all five Source certificate structures. The
storage-copy witness loads a live two-element uint8 array, allocates a fresh
memory parent, preserves the old heap object and observes values 7 and 11;
index 2 panics. Bytes defaults preserve nonheap state. Timeout controls retain
the input state. These are Source executions, not a Source-to-backend
representation or compiled-code theorem.

`SourceSize.lean` derives the oversized-length panic at the reached evaluation
state. Concrete controls distinguish zero-length success, oversized-length
panic and horizon timeout. The generic theorem permits a changed reached
state; the concrete local-expression witness has no side effects.

Independent finder and skeptic reviews checked the strengthened root/gap
contract, positive inhabitants and removal of the assumed local panic result.
Per-file diagnostics pass; full checkpoint validation is recorded separately.
Full G33/G35 implementation, total size-failure coverage, recursive traversal
and mixed-location composition remain open.
