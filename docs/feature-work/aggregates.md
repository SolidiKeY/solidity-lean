# Aggregates

Inline arrays, fixed memory snapshots, reference tuples and slice effects.
Inventory status: partial. Primitive slice materialization, internal
passing/returns and hashing are in
[calldata-slice-copies.md](../calldata-slice-copies.md); calldata aliases in
[calldata-slice-copies.md](../calldata-slice-copies.md#calldata-origins-and-aliases).

## Supported

- **Inline arrays** allocate fixed memory, then evaluate and store each element
  in source order. The type starts at the first mobile element type and folds
  Solidity's implicit common type, independently of the target (`[1,256]` is
  `uint16[2]`; a `uint16[2]` target does not make `[1,2]` stop being
  `uint8[2]`). Numeric, Boolean, fixed-byte, finite nested-array and struct
  elements. Storage reference elements copy at each element's evaluation;
  memory references alias (`Examples/Tactics/Aggregates.lean`,
  `AggregatesImport.lean`).
- **Fixed memory snapshots** (`Src.fixedCopyMem`, with its `MPath` and
  `FixedCopy` witness) compose memory-to-storage copying with the fixed-shape
  conversion; `Src.lower_valueT` and `Src.valueT_wk` cover them. They may copy
  into compatible dynamic or longer fixed storage arrays, reference pushes and
  deferred getter receivers. Storage value copies may widen numeric element
  widths; aliases and memory bindings keep exact shapes. Evaluation stays after
  the receiver's effects when the native receiver statement defers it.
- **Tuples.** Local memory and storage-alias tuple targets capture every RHS
  reference before rebinding. Calldata read-only propagation includes nested
  assignment roots and is computed to a finite fixed point.
- **Slices** (`Examples/Tactics/AggregateSlices.lean`). The base is captured
  before the endpoints and stays stable through rebinding; nonconstant bounds
  are read once; relative bounds are checked before outer offsets are added.
  An invalid relative index uses the base's out-of-range index, so the bounds
  `Panic(0x32)` is kept without evaluating an overflowing offset. Endpoint range
  failures are ordinary reverts. Legacy schedules right-first and via-IR
  left-first. Reference: solc 0.8.38
  `YulUtilFunctions::calldataArrayIndexRangeAccess`.
- Reference pushes check captured source widths against the receiver or the
  deferred getter's return metadata.

## Refused, and why

- Byte-width widening in a snapshot copy: it needs shifting values.
- Multiple nonlocal, effectful/dependent and duplicate tuple targets.
- A whole literal as an assignment target (indexed temporary elements stay
  writable).
- The generic fixed-copy adapters are Lean-only: the KeY fragment and the EVM
  compiler exclude them, as they exclude the storage fixed-copy adapters.

## Cost

Stable slice captures and relative checks made a nested slice read cost more
to check (one sample: 0.90 s to 1.06 s); no heartbeat limit was raised.

## Left

- Reference-element slices, general writable whole-calldata copies, external
  calls with reference arguments.
- Heterogeneous reference-return tuples (a function-return interface).
- Nominal enum/UDVT and function-valued element identities; recursive shapes
  ([recursive-types.md](recursive-types.md)).
