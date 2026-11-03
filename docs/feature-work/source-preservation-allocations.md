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
  succeed. `EncodingVariants.lean` covers the remaining encoding arms below.
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

`Controls` is the aggregate root of the original controls.

`Preservation.evalE_abiKind_mem` in `EncodingVariants.lean` covers all four existing encoding kinds
(`abi.encode`, packed, selector and signature), under the original `argsOK`
and an argument-evaluation MemOK triple. Success retains MemOK and returns a
valid reference; every halt retains MemOK. Selector conversion uses the original
implicit bytes4 condition. This proves preservation, not encoding success or ABI
correctness. `EncodingVariantControls` observes actual typed encodings in both
pipelines over a nonempty heap, including exact allocation/caller state and
missing-head refusals. Its preservation triples are stated for an arbitrary
heap typing. `packed_inhabited` applies `packed_mem` to `initial_mem` with
the empty heap typing over that nonempty heap, obtaining post-state MemOK and validity of the actual
allocated bytes reference in both pipelines. The signature digest stays
parameterized by Fixed.

`Preservation.eval_new_fragment_mem` in `NewArrayFragment.lean` consumes the published V16
`eval_new_mem` rule and discharges its child-memory premise with the existing
checked call-fragment theorem. It covers a standalone new-array parent whose
indexable length belongs to that fragment; it does not add allocating nodes
to `ValFragC`. `NewArrayFragmentControls` computes the length as two plus two,
allocates object 1 while preserving the live caller reference to object 0, and
checks the allocation panic for an oversized computed length in both pipelines.
The compound expression times out at source horizon 3 and succeeds at horizon 4;
both observations are retained. Independent finder and skeptic reviews found
no confirmed defect in this consumer or its controls.

## Additive memory-expression and reference-return subset

`AllocatingFragment.lean` defines `AllocatingExpr` over the existing intrinsic
`RExpr`. It includes the original value fragment with its operations check,
reference locals, same-type conversions, conditional reference results and
`newArray` with an admitted length. `eval_allocating_mem` proves `MemOK` and
result validity at every horizon, including every halt. This is a separate
syntactic admission; it does not change `ValFragC` or its statement checker.

`ReferenceArguments.lean` admits exact-type converted argument lists. Its
`eval_exact_args_mem` preserves an earlier argument's reference witness when a
later argument allocates. Cross-type conversions are outside this admission.
`AllocatingControls` exercises alias and fresh-reference branches, allocation
panic, timeout, a retained caller prefix and a later-argument allocation in
both source pipelines. Raw string literals remain outside `AllocatingExpr`.

`ReferenceReturns.lean` derives body preservation for `returningBody`: a
modifier-free body containing one `retTuple` of exact-type admitted expressions.
`call_returning_mem` consumes the actual selected-body equality and handles
argument packing, default return-slot allocations and actual return-slot writes.
`sub_returning_mem` restores arbitrary valid caller locals across success and
all halts. `eval_call_returning_mem` lifts this through the actual `RExpr.call`,
with its original `fnSig` equation and exact-type argument admission. Calls
inside these expressions still use the original `CallsOK` value catalogue;
there is no assumption that arbitrary reference-callee bodies preserve memory.

`ReferenceReturnControls` supplies a hand-built intrinsic runtime program with
a matching direct-call signature, not an elaborated-program certificate. The
parameter aliases object 0, default result slots allocate objects 1 and 2, and
the body returns alias 0 plus fresh object 3. The controls consume the call and
expression preservation theorems, check restored caller locals and escaping
reference validity, and retain the exact low-horizon timeout. An oversized
allocation panics after the two default allocations; `panic_preserved` applies
the same call theorem to that halt with heap-next 3. Independent
finder and skeptic reviews found no confirmed defect in this additive subset.

## Memory statements and internal bodies

`MemoryExpressions.lean` extends this admission with same-type local rebinding
and primitive memory-array writes. Array base, index and right-hand side must
belong to `AllocatingExpr`; writes retain the evaluator's bounds and location
checks. Rebinding a pointer changes that local, while writes through an alias
change the shared object. Reference-element writes are outside this admission.

`MemoryBodies.lean` defines syntactic `MemoryStmt` and `MemoryItems`
certificates. A joint horizon induction derives `MemOK` and outcome-local
validity for declarations, admitted expression statements, exact-type returns,
blocks, conditionals, sequences and unchecked blocks. Conditional evaluation
uses `BodyExpr`, retaining condition updates and heap effects before executing
the selected branch; branch scope is then closed. Existing value-fragment statements
retain their original operations and call premises. The proof covers every
success and halt; declaration admission does not assert allocation success.

`MemoryBodyCalls.lean` derives modifier-free body preservation from these
certificates. `call_memory_body_mem` handles actual argument packing, default
return slots and result extraction; `sub_memory_body_mem` transports valid
caller references across heap growth. `eval_memory_call_mem` consumes the
actual selected-body equality, signature, parameter/result types and initial
frame-layout equation. No callee memory-preservation oracle is assumed. Calls
inside admitted expressions still use the original value `CallsOK` catalogue;
this does not recursively admit memory-body calls.

`MemoryBodyControls` uses a hand-built intrinsic runtime program with a matching
signature, in both source pipelines. Two parameters alias object 0; a write is
visible through the other alias, rebinding one parameter allocates a distinct
object, and the returned alias remains valid after caller restoration. A
bounds failure retains the already allocated default return slot and restores
the caller. A separate block allocates a default bytes object and an initialized
array, then restores its incoming local frame. Preservation theorems consume
these actual evaluator equalities over inhabited, nonempty memory. Timeout is
also retained. Independent read-only finder and skeptic reviews found no
confirmed soundness defect.

`MemoryBranchControls` checks both branches of an actual conditional: one
allocates block locals and restores its frame, while the other persistently
rebinds a reference parameter. An effectful Boolean condition updates the local
seen by the selected allocating branch. The same bounds-failing write is skipped
on a false condition and panics on a true condition. All preservation conclusions
consume the corresponding exact evaluator runs on inhabited memory, in both
pipelines. Finder and skeptic reviews found no confirmed soundness issue in the
conditional induction; these controls do not imply frontend or compiler admission.

## Allocation parents in memory bodies

`BodyExpr` also admits struct construction and inline-array literals with
`ExactArgs`, and every existing ABI encoding kind with `EncodingArgs` and its
original `argsOK` check. `EncodingArguments.lean` derives argument preservation
from `AllocatingExpr` children and raw string literals, in the actual evaluator's
left-to-right order. The struct and inline-array parents derive their child
triples from exact-type argument admission. Field packing, one-word elements,
ABI eligibility, horizon and allocation halts remain unchanged. Encoding
preservation does not assert successful encoding or general ABI correctness.

These parents can occur in admitted expression statements, initialized
declarations and conditional conditions where types permit. Their children
remain the narrower `AllocatingExpr`/`ExactArgs` admissions; the change does not
allow every `BodyExpr` constructor recursively in arbitrary argument, rebinding
or return positions. Returning a previously bound reference retains the
existing exact-local admission.

`AllocationBodyControls` composes actual typed struct, inline-array and packed
encoding nodes in a statement block over a nonempty memory prefix. It consumes
`memory_body_at` and observes the exact three new objects and restored frame.
Selector and signature controls consume the new parent rule and existing exact
runs. A packed encoder evaluates an allocating child before allocating its own
output; a second child that panics leaves the first child's allocation in place.
Missing-head eligibility remains false and the existing named `abi arguments`
halt is retained. All observations run in both source pipelines and the
preservation consumers have inhabited inputs. Independent finder and skeptic
reviews found no confirmed defect; neither inferred frontend, progress or
compiler coverage from these source controls.

Not covered: arbitrary reference-call bodies, whole-program admission of this
memory subset, unrestricted allocation nesting or cross-type argument conversion, progress or termination,
compiler/EVM refinement, `SourceSpec` and rollback. The existing standalone
allocation-arm rules above retain their stated premises. All printed axioms are
`propext`, `Classical.choice` and `Quot.sound`.
