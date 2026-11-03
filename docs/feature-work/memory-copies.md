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
The published `Interface.lean`, `InterfaceV2.lean` and `Premises.lean`
remain byte-identical to the integration base. `SourceInterface.lean` is a
compatibility import; the existing Source certificate definitions stay in
`Interface`, including its published `Source.Hoare` import.

`InterfaceV2Roots.lean` adds an optional `StorageWordRootCertificate` companion
to an existing V2 word certificate. It fixes `base' g.val.id = cursor` and
preserves each old `Objects.Gap` below the cursor without changing V2's fields
or strengthening its existing `correct` projection.

`NewArrayLengthPanicPremise` retains all four published fields, including
`failure`. The additive `NewArrayLengthPanicInputs` in `SourceSizeInputs.lean`
has only length evaluation, successful conversion and the oversized condition.
`SourceSize` derives its panic equation and constructs the unchanged public
premise. Neither the public failure projection nor Source semantics is replaced.
Finalize-allocation/cursor-overflow semantics remain S03-PANIC41 obligations.

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

Earlier finder and skeptic reviews checked the root/gap contract, positive
inhabitants and derived local panic result. Fresh independent finder and skeptic reviews found no semantic/API defect in
the additive correction. They verified byte-identical published interfaces,
independent panic inputs, the existing public result type and an inhabited
optional root/gap companion. Neither used Lean, builds or edits. All six
changed/new modules have zero MCP errors; the five input/proof/control modules
have no warning diagnostics. Checkpoint gates and axiom audit remain required.
Full G33/G35 implementation, total size-failure coverage, recursive traversal
and mixed-location composition remain open.

## Source traversal frame interface

`SourceFramesInterface.lean` states the next local obligations: nonheap state
is unchanged, the heap frontier grows monotonically, and every old object
retains its identity and contents. The default and storage-load families range
over every Source type and horizon, including bytes/string, nested aggregates
and recursive declarations. Outcomes are those of the existing interpreter;
these signatures neither guarantee success nor impose a new shape filter.
`Source.Horizon.Grow` and `Const` preserve events and do not prove heap growth.
The proofs must use the existing Source allocation and Hoare operations.
Physical compilation, size/finalization failures, and layout agreement remain
separate obligations; no missing producer result is assumed here.

`SourceFramesCore.lean` proves allocation-frame composition through the existing
Source bind rule and proves the allocator and typed storage reads preserve that
frame. `SourceDefaultFrames.lean` discharges all four default traversal fields;
`SourceStorageFrames.lean` discharges all five load traversal fields. These
proofs quantify over every environment, locals context, Source type, path and
horizon. They retain the real success or Halt and its reached state, even when
a child was allocated before timeout. No capacity, success or producer premise
is required for these frame laws.

`SourceRootCopies.lean` derives the complete fresh-parent Source copy
certificate from an explicit successful `loadMem` execution; its frame and
freshness observations are proved, not independent assumptions. Requested
memory type/path agreement with compiled storage layout is still separate.
`SourceFramesControls.lean` uses a declared dynamic storage array of bytes:
two empty bytes child objects are allocated at 1 and 2 and the copied parent at 3, while
the old Boolean at 0 and all nonheap state are preserved. The parent returns
the distinct child references, and index 2 panics. A fixed memory array of two
bytes references also has an inhabited default certificate. Lower horizons
time out after the first child allocation; the reached heap differs from the
input heap and is never silently rolled back.

These are Source traversal/frame and fresh-parent results. They do not prove
physical emitted-code correspondence, total successful traversal, contents for
every graph, checked allocation-size/finalization failures, or whole G33/G35
coverage. The remaining compiler and representation work stays open.

Independent read-only finder and skeptic reviews found no semantic defect in
these Source frame laws or controls. Both retain the compiler/layout/size
boundaries above. The bytes children are empty; this control does not establish
populated byte-payload copying.

## Published-interface compatibility

The integration receipt rejected a theorem named like the existing `failure`
projection. The additive correction preserves all existing public definitions,
fields and import paths, using separate input and optional root/gap records.
The signature-only companion commit precedes their constructors and controls.
No Source, admission, exclusion, dependency premise or proof budget is changed.
