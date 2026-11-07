# Nested fixed-child deletion

`SourceUintFixedRefsDelete.lean` consumes the existing fixed-reference parent
observer and the actual nested lvalue/write adapter. `resolved_delete` resolves
the actual Source `.delete` expression and its unit-result statement. The
published `Source.deleteLoc` obtains uint zero and calls `writeLoc`; this agrees
definitionally at the sufficient horizon with the existing primitive default
write. No evaluator, heap, deletion semantics or target producer is replaced.

`write_delete_items` executes an actual nested assignment followed by actual
nested deletion as one existing `Source.execItems` program. Initial local
alignment, typed parent selection, in-range child index, MemOK and the
same local selected-address separation suffice. The second alignment, parent
index, sibling separation, observer and MemOK derive from the actual first
output; neither a desired reached relation nor a second execution is a premise.
The generic fixed length and runtime parent/index/value remain unbounded by any
new public cap. A zero-length fixed child has no valid index under these premises;
this theorem does not admit zero-length fixed Source declarations.

For arbitrary base horizon h, the two statements run at h+6 and h+5 and the
combined Items at h+7, with the original explicit nps. These are sufficient,
not minimal horizons. Both reached typed heaps and Source states/observers are
returned. Final MemOK, locals, parent, all distinct typed objects and Source
addresses, heap.next and ex/events/logs/fnLocals are derived from the two runs.
Repeated occurrences of the same selected identity remain supported. Separation
only concerns different children occurring in this parent, not global injection.

The inhabited `nested_mutation_delete` client runs both existing pipelines from
parent [LEFT,LEFT,RIGHT], LEFT [7,0,max] and RIGHT [8,9,10]. It retains the actual
changed prefix LEFT [7,42,max] and final LEFT [7,0,max], both complete three-object
Source tables, all locals, sibling objects, heap bound and world fields. An
explicit inequality distinguishes skipping deletion. `nested_delete_zero_horizon`
proves the actual timeout retains any reached state before execution; no outer
transaction rollback is inferred. Existing full read/write/bounds/empty-parent
and stale/type observations remain intact.

Both producer laws and both new clients have measured exact standard-axiom pins
[propext, Classical.choice, Quot.sound]. Core02 failed only because the Items
header omitted its intrinsic context/mode annotation; core03 fixes that annotation
without a statement or budget change. All failed receipts remain preserved.
Independent source and committed-artifact reviews are recorded in the delivery.

This is Source Items plus typed Heap.writeAddr correspondence. No intrinsic Prog,
nested pointer/index emitted word append, physical-byte program, general allocation
failure, compiler/EVM or whole-lane adequacy is established. Full original gates
and G32/P6b/G34/G35.02 reference remainder/G35.03/Backfill A/B remain partial;
G33 and G35.01/.04/.05/.06 remain delegated/open. The goal stays unchanged BLOCKED.
