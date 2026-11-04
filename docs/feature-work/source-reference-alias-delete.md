# Computed reference replacement, reached alias, then deletion

`SourceBoolRefsAt.computed_alias_delete_program` in
`Backend/MemoryOps/SourceReferenceAliasDelete.lean` composes three actual operations:
compute `src[j]` and replace `dst[i]`, select that reached element into a local,
then delete its Boolean element `k`. Initial independent observers, root/index
alignment, bounds, MemOK and full RefArrayStateRepr derive every intermediate
execution and representation. No successful suffix or desired final relation is assumed.

The sufficient initial selected-footprint condition separates Source addresses of
distinct selected Boolean children. Repeated aliases are permitted. This is neither
global address injection nor a source admission restriction. Typed local separation
preserves the scalar operand through reference rebinding.

Actual Source statement horizons are `fuel+6`, `fuel+5`, `fuel+4`; the single
three-statement RItems program uses `fuel+7` and ORIGINAL Source context length
as nps. Intrinsic Prog and the complete existing symbolic-word append execute the
same reached operations. Final parent/child correspondence, other Boolean objects,
Source other addresses/next/ex/events/logs/fnLocals, locals, saved stack and the
allocator follow from the initial premises and actual outputs. Allocator transport
retains positive base, space and initial live-parent bounds.

Both pipelines and same/distinct parent cases instantiate the general theorem.
Controls retain all prior vectors and add all five Source/native objects and all
24 words at four stages. RIGHT element1 changes true to false only after deletion;
LEFT element0 remains true. Separate reached read expressions prove these values;
they are not a fourth compiled statement. Skipped-delete/stale-LEFT negatives are
complete-vector comparisons, not a claim of reversed Source execution.

Exact measured guards: the typed scalar-frame helper has no axioms; the general
composition and both inhabited controls use only propext, Classical.choice and
Quot.sound. Kernel and symbolic-word evidence does not establish external compiler,
EVM, physical-byte execution, general recursive graphs, ABI/storage, deep-copy,
transaction rollback or full Source/V10/target closure. Original queues remain partial.
