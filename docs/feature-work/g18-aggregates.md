# G18.02/.03 aggregate consumers

Consumers of declaration graphs and memory representations for aggregates
(`Backend/Aggregates/G18*.lean`), from the v16-correctness-transfer lane. The
headline theorems are quantified over the environment, context, state, heap,
base and machine.

## Proved

- `G18Storage.lean`: `Env.pathTy` suffix composition and array/mapping/struct
  step typing. Typing only: fixed-array path typing has no bounds check.
  `DeclarationRoots` is a declaration/type interface with no instance yet.
- `G18Graph.lean`: `DeclarationGraph` field lookup, storage-path and
  memory-layout field typing (`fields_lookup`, `graph_field_type`,
  `graph_storage_path`, `graph_memory_field`).
- `G18Memory.lean`: `nested_write_observe`: a nested `bool` child write with
  every reached alias observation on the Source and word machines.
- `G18ReferenceSequence.lean`: `rebind_then_mutate`: parent pointer rebinding
  followed by mutation of the reached child.
- `G18Physical.lean`: ordered `uint`-array observations, write postrelation
  and a live REVERT endpoint over `UintArrayAt` (P6). Source panic bytes and the
  word-IR revert are kept apart, not equated.

## Fixtures

- `G18MemoryClient`: parent `[q, q]`; the separation premise is vacuous there.
- `G18DistinctClient`: `[c0, c1, c0]`, non-vacuous separation; the final writes
  commute, so their order is not witnessed.
- `G18PhysicalControls`: the `uint` array `[7, 8]`, update 7 to 255, ordered
  vector `[8, 255, 8]`.
- `G18GraphRootControls`: the single-node `Cell` certificate from
  `Lowering/V07/GraphControls.lean` with a storage variable root; graph clients
  and wrong root/key/field rejections.
- `G18Controls`, `G18DistinctControls`: step-typing checks, sequencing and
  wrong-candidate rejections.

## Open

G18.02 storage execution, broader G18.03 constructors, composed parent/child
traversal, physical byte EVM, rollback and allocator theorems. G18.01
declaration extraction stays with the V07 lowering.
