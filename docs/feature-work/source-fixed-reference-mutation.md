# Fixed-reference parent mutation

`SourceUintFixedRefsWrite.lean` extends the genuine fixed Source observer from
`SourceUintFixedRefsMemory.lean`; it does not cast fixed arrays to dynamic arrays.
`same_heap` transports the observer across local contexts without asserting local equality.
`write_child` derives the whole reached observer from actual typed `Heap.writeAddr`
and actual Source `writeLoc`, preserving MemOK, heap.next, parent references,
other typed objects, other Source addresses, locals and world fields.

The sufficient address premise separates the selected child from distinct typed
children occurring in this parent. Repeated occurrences of the selected identity
remain allowed. This is neither global address-map injection nor a new admitted
profile restriction; necessity for no-op writes is not asserted.

`eval_nested_loc` resolves the actual nested indexed lvalue at horizon+3.
`resolved_write` executes RHS-first assignment at horizon+4 and its discarded-result
statement at horizon+5, with the original explicit nps. Both inputs and the old
child correspondence come from the initial observer; no final correspondence or
second successful execution is a premise. These are sufficient horizons, not
minimal-fuel or source-admission bounds.

`mutation_initial` and `nested_mutation` inhabit both existing pipelines with
parent references [LEFT,LEFT,RIGHT], LEFT [7,0,max] and RIGHT [8,9,10]. The actual
write changes LEFT to [7,42,max]; a reached nested Source read returns 42. Complete
three-object Source tables, all locals, heap.next=3, absence of further objects,
typed contents, sibling identity/content and ex/events/logs/fnLocals are observed.
Existing read/bounds/timeout/empty-parent/type controls remain intact. This file
adds no intrinsic Prog, Source RItems, emitted word or physical byte program.

Four producer laws and two clients have measured exact standard-axiom guards
[propext, Classical.choice, Quot.sound]. The first control check failed on an
opaque literal-list length and an unreduced canonical index; controls02 passes
after explicit length simplification and definitional index reduction. Raw failed
receipts remain retained. Independent finder and skeptic source reviews found no
soundness issues; committed-artifact review is recorded separately in the delivery.

Full lane gates and final Source/V10/target/world/compiler adequacy remain open.
G32/P6b, G34, G35.02 reference/struct/recursive remainder, G35.03 and both Backfills
remain partial; G33 and G35.01/.04/.05/.06 are delegated and open. Public primitive
copy certificates do not complete the reference remainder. No goal status changes.
