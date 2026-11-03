# V10 storage operations

Storage copy, clear, push and pop over the existing storage graph, numeric
word store and structured `Evm.Instr` target (`Backend/StorageOps/`), from the
v10-storage-operations lane. No Source, compiler or bytecode layer is involved:
the core is Source-free.

## Layers

- Runtime-shaped graph operations: `Traversal.copyArray`/`copyAt`,
  `RecursiveCopy.recursiveCopy`, `RecursiveClear`, `RecursivePop`, each proved
  equal to the master semantics (`copyArray_eq_overlay`, `copyAt_eq_semantics`,
  `recursiveCopy_eq_overlay`).
- Prefix transport and disjoint-path commutation (`CommonPrefix`,
  `PrefixLaws`, `PathOperations`, `Commutation`, …); push/pop/delete
  lifecycles (`Lifecycle*`, `MixedLifecycle`, `CopyLifecycle`).
- Operations against the `Represented` relation (`PathRepresentation`,
  `Copy*`, `Clear*`, `RepresentedOperations`); scalar save/copy to numeric
  stores and `Evm.Slot` (`TargetOperations`, `KeysFit`).
- Numeric transport with per-run regions (`FiniteRun`), footprints and G27
  layout access (`NumericTraversal`, `CopyTransport`, `CopyWrites`,
  `LayoutAccess`).
- Structured target loops and correspondence (`TargetArray*`, `TargetCopy*`,
  `TargetNested*`, `TargetFixed*`, `TargetSnapshot*`), snapshot frames,
  nested-array root composition (`OutputRootComplete.complete`, whose
  `reads`/`writes`/`clearWrites` premises cover intermediate copy states).
- Runtime-header repetition and footprint shrinkage: `RuntimeCopyRepeat`
  (`headers_and_footprint`, `copy_repeat`), `RuntimeCopyComposition.complete`,
  `TargetArrayRepeat.complete`, quantified over machines, slots, lengths and
  `FiniteRun`.

Premises catalogue: the `FiniteRun` per-run region, `KeysFit`, the
`targetInitial` correspondence, self-copy or separation. Retained
counterexamples: overlap refutes repetition, a region collision, header
interference. `*Controls` modules instantiate the premises
(`RuntimeCopyRepeatControls` builds a real `FiniteRun 128 16 2`).

## Open

Source bridges for delete/copy (the lane's Source-side results are not on
master), emitted recursive traversal, packing and ABI, world rollback.
