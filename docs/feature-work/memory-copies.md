# Memory defaults and copies

`Solidity/Backend/MemoryCopies/**` holds a partial, signature-only draft for
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
`Interface.lean` also gains Source-side default, storage-load and outcome
certificates indexed by the actual Source run. Tying `cost` to the copied
object's allocation size is still open, no V2 certificate is inhabited yet
(only negative laws), and V2 `StorageWordCertificate.correct` does not pin the
pushed address to the old cursor or keep V1's `Gap` clause. The new V1
Source certificates are not yet inhabited; `NewArrayLengthPanicPremise.failure`
assumes the panic equation.


## H44 bounded code-only increment MC01

This first dependency-ordered increment contains17 owned changed Lean modules, including7 Controls files, plus the generated root, owned module-map rows and12 owned standard axiom pins. It preserves the previously reviewed source bytes; no theorem, premise, gate or proof budget is changed. Original signature/proof history, the remaining12 increments and unfinished nested-location-pipeline work remain in `/workspace/memory-copies` on the preservation branch recorded in the manifest. Full G33/G35 remains open.

Bulk is not part of this increment. The only new lane test file is [the H44 archive manifest](../../tests/memory-copies/H44-BULK-MANIFEST.json), recording absolute VM archive path, byte size and SHA256. Generated evidence, corpora, fixtures and logs stay on the original VM. The archive is transport/storage only and is not claimed as proof.

Modules and controls:

- `Solidity.Backend.MemoryCopies.NestedDefaultControls`
- `Solidity.Backend.MemoryCopies.AliasBindingInterface`
- `Solidity.Backend.MemoryCopies.AliasBinding`
- `Solidity.Backend.MemoryCopies.AliasBindingControls`
- `Solidity.Backend.MemoryCopies.AllocationPanicInterface`
- `Solidity.Backend.MemoryCopies.CheckedDefault`
- `Solidity.Backend.MemoryCopies.CheckedDefaultControls`
- `Solidity.Backend.MemoryCopies.CheckedReference`
- `Solidity.Backend.MemoryCopies.CheckedReferenceControls`
- `Solidity.Backend.MemoryCopies.HeapContents`
- `Solidity.Backend.MemoryCopies.HeapContentsControls`
- `Solidity.Backend.MemoryCopies.DeepCopyContents`
- `Solidity.Backend.MemoryCopies.RuntimeArrays`
- `Solidity.Backend.MemoryCopies.RuntimeArrayControls`
- `Solidity.Backend.MemoryCopies.RuntimeRebindInterface`
- `Solidity.Backend.MemoryCopies.RuntimeRebind`
- `Solidity.Backend.MemoryCopies.RuntimeRebindControls`

Validation is recorded in the external handoff. Existing Source/physical/gas/recursive/compiler and typed producer obligations remain unchanged. Source root collision and global trust/pin drift are retained as external blockers, not waived.
