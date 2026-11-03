# V10 storage operations

Storage copy, clear, push and pop over the existing storage graph, numeric
word store and structured `Evm.Instr` target (`Backend/StorageOps/`), from the
v10-storage-operations lane. The core is Source-free. Above it, `Lowering/StorageOps/` checks actual
independent Source storage operations; these are operation correspondences,
not a general compiler or bytecode refinement.

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

General Source AST/compiler/address/liveness correspondence, emitted recursive
traversal, packing and ABI, world rollback.

## Source operation clients (C145)

Registered `Lowering/StorageOps/SourceCopyCommutation.lean` uses the
independent Source semantics and the existing copy operation log. Its four laws
prove exact runtime touched-path frames, overwritten-word independence,
pointwise transport and all-path word commutation for disjoint destinations
and fixed captured payloads. Ordinary storage is explicit. Older shadows and
missing outside cells remain observable; journals and full states do not commute.

`Lowering/StorageOps/SourceCopyCommutationControls.lean` executes both actual `Source.storeVal`
orders with shrinking/growing arrays and complete ordered observations.
Distinct journal snapshots refute state equality. Same-target and incremental
source-capture orders discriminate the premises; rollback is explicitly invoked.
These clients are registered above the Source-free Backend core. They do not
supply general compiler, target, physical-address or world equivalence. Ten
Source modules are migrated with unchanged proof bodies and declaration names;
legacy script import wrappers preserve their clients.

## Operation views and Source clients

`Value.overlay` is the independent graph specification. `Traversal.copyArray`
provides outer runtime-prefix transport, using the semantic slot operation at
nested leaves. `RecursiveCopy` and `RecursiveClear` independently recurse at
nested demanded values. Their correspondence laws identify these views; lazy
function-valued fields do not establish eager emitted traversal of a whole
aggregate.

`Lowering/StorageOps/SourceScalarDeleteLog.lean`,
`Lowering/StorageOps/SourceArrayDeleteTarget.lean` and
`Lowering/StorageOps/SourceStorageCopy.lean` supply actual Source delete/copy
execution laws, frames and explicit rollback. Source repetition and commutation
clients preserve complete ordered observations and distinguish journal/state
identity. These modules import published Source semantics above the core;
representation, target and whole-program premises remain explicit.

`Backend/StorageOps/TargetSelfCopy.lean` is the target-only self-copy interface.
The old module and theorem namespace remain compatible; the canonical namespace
exports the same laws. `OutputRootComplete.complete` requires read/write/clear
location coverage over intermediate stores as well as OLD graph observations.

The remaining actual Source clients are registered above the core: scalar,
integer and boolean array deletion with represented target clearing; signed,
boolean and fixed-array copying with captured snapshot target observations;
mapping barriers, Source self-copy and two-destination deletes. All 42 legacy
script imports remain compatible. Module registration preserves their proof
bodies, exact fuels, typed path/read/layout premises and complete ordered
positive and negative controls. These component correspondences do not close
general Source compiler, recursive emitted traversal or world refinement.

The Source and target self-copy modules retain a shared historical namespace
with disjoint declaration names. Their module paths and import layers remain
separate; the canonical target namespace exports only the five target laws.

`Backend/StorageOps/LoopLaws.lean` shares the condition/body turn, zero-guard
exit and single-loop adapters used by five runtime loop modules. Their ranking
and prefix proofs still establish the required `loopRun` result. The clear
condition reuses the published memory range condition with the same instruction
list. Populated controls pin complete ordered context observations, false-guard
body avoidance, pending-jump and malformed-flag faults, and one actual terminating
loop. Shared adapters alone do not prove arbitrary-loop termination.
