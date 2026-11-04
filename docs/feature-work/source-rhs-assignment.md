# A memory-writing RHS before the outer assignment location

`Backend/MemoryOps/SourceRhsAssignment.lean` consumes the existing independent
Source assignment evaluator and checked primitive assignment/word certificates.
`rhs_assign_success_word` and `rhs_assign_late_bounds_word` start with INITIAL
SourceBoolMemoryAt, local alignment, actual bounds, MemOK and StateRepr. They
derive the real inner write, reached outer alignment/length/observer and second
operation; no reached relation/run/output is assumed. The factoring helper is
instantiated only with those derived executions.

The actual Source syntax is `root[outer] = (root[inner] = rhs)`. The inner
expression runs at fuel+3, whole expression at fuel+4 and ONE discarded-result
Source statement at fuel+5, with original Source context length nps. The Source
expression's Bool result is explicit. Matching native Prog has TWO statements;
the whole existing word-code append certifies only the discarded-result statement,
not a general assignment-expression result compiler or arbitrary side-effectful RHS.
Reloading the unchanged scalar local is justified by the actual first producer's
local/environment frame. Runtime lengths/indices remain general under intrinsic
validity; no new source admission cap, profile or injectivity assumption appears.

Late outer bounds failure retains the actual RHS-write Source state. Native/word
error outcomes erase the final machine; their successful prefixes remain separately
executed witnesses. No transaction rollback or panic-byte equivalence is inferred.
The generic RHS write may be same-value; material change is established by the
controls rather than required universally.

Both pipelines inhabit the populated old fixture with LEFT[T,F,F], RIGHT[F,T,F],
old[LEFT], source[LEFT,RIGHT,LEFT] and empty[]. An INITIAL represented Bool true
local occupies cell7 (not the earlier guard99), and outer index is initially0
or3. No declaration/local-update Source execution is claimed for this setup.
RHS LEFT[1]=true changes false to true. Outer endpoint3 then fails; a separately
executed INITIAL outer evalLoc fails before any write, and actual Source heap
inequality distinguishes evaluation order. Success really writes outer0=true,
which is a same-value second write; final-only commutation is not an order test.
Complete five-object Source/native tables and all24 INITIAL/RHS/success-final
words retain aliases, neighbour, free48 and stack42. `rhsFinalWord` is GOOD-case
only; the failing run exposes only its real `rhsMidWord` prefix. Low horizon2
actually times out before the inner write. Prior vectors/bodies/guards are intact.

Eight exact measured standard-only guards cover the new laws and controls.
Source world/events/logs/fnLocals/locals, other addresses, typed object frames,
legacy StateRepr and allocator transport follow from actual outputs. This local
memory observation does not establish full Source-world representation, reference
or recursive graphs, ABI/storage/copy/physical-byte/emitted compiler/EVM adequacy.
Original queues and final full-lane validation remain open.
