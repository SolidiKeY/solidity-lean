# Source allocation and frame preservation (SS-CP2)

The modules in `Solidity/Source/Preservation/` reuse `WellTyped`'s `MemOK`
(typing, object shape and bare-value elements), the ABI decoder's existing
preservation and `storeOK`. Source representations, interpreter operations,
allocation inputs and halt policies are unchanged.

## Frames

- `Frames.sub_mem` preserves the caller's memory validity across `EM.sub`, on
  success and on every halt. It assumes valid entry locals and callee
  preservation for an arbitrary initial heap typing; it does not prove callee
  preservation. Heap extension carries the restored caller's references.
- `sub_locals` proves exact restoration of the caller's locals, whatever the
  result.

## Allocating expressions

- `AllocationSites`: string literals materialize through `convRV` into
  bytes/string memory. Raw literals do not allocate.
- `MemberPacking` checks counts and types through `fieldsOf` and produces
  matching bare members. `evalE_structNew_mem` composes this with allocation,
  relative to preservation and validity of the arguments.
- `Encoding` preserves memory through byte reads and encoders, including
  storage reads. `evalE_abiEncode_mem` covers `.encode`, relative to argument
  preservation. Every existing halt is kept; encoding is not claimed to always
  succeed. The other `abi.encode*` arms are not yet proved.
- `ArrayLiterals.evalE_inlineArray_mem`: converted arguments become matching
  bare elements through `inlineData` before allocation. Reference elements keep
  the constructor's `oneWord` type-level gate.

## Joint preservation

`Fragment.fragMemAt` closes the joint horizon induction over the existing
fragment, unchanged: expressions, lvalues, converted arguments, statements,
loops, modifier-free bodies and internal calls. It uses the original `CallsOK`
and needs no recursive memory-preservation assumption. The fragment has no
memory operations and its results have value types (`expr_result_ok`), so the
content of this induction is frame restoration and heap growth; the
allocating arms above are not part of it.
- On success, `evalE_fragment_mem` returns full memory validity, current-local
  validity and `RValOK`. On every halt it returns full memory validity.
- `progress_and_preservation` pairs this with the existing progress theorem,
  whose frame premises are unchanged.

## Controls

- `AllocationControls` covers an actual two-field struct constructor (`Typed.toR`) and
  primitive ABI encoding in the legacy and viaIR pipelines. Count and type
  mismatches keep their named `stuck` outcomes.
- `FrameControls` allocates before success and before revert.
  `CallerReferenceControls` shows that a caller reference at object 0 survives
  the allocation of a distinct object 1.
- `StorageCopyControls` copies along distinct layout paths into a nested
  `uint256[][]`, which forces `storeVal` to allocate the inner copy. The reads
  are heap-next 1, outer length 1, inner length 2, values 7 and 9.
- `ArrayLiteralControls` uses Boolean literals in both pipelines.
- `FragmentControls` starts from an actual elaboration with a nonempty heap
  and a caller reference. The nested call uses a checked complete P9
  catalogue; the recursive call uses `RecursiveControls`' allowlist. Both nested
  success and a recursive timeout preserve that memory prefix.

`Controls` is the aggregate root of these controls.

Not covered: reference arguments and returns in the expression fragment,
allocating expressions inside the fragment, termination,
compiler/EVM refinement, `SourceSpec` and rollback. All printed axioms are
`propext`, `Classical.choice` and `Quot.sound`.
