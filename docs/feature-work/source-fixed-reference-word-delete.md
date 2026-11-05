# Nested fixed-child whole-word deletion

`SourceUintFixedRefsDeleteTarget.lean` proves
`SourceUintFixedRefsAt.resolved_delete_word` and
`SourceUintFixedRefsAt.resolved_write_delete_word`. The first reuses actual Source
uint default/delete evaluation, actual intrinsic primitive delete (via the
published `deleteMem_primitive_eq_assign`) and the existing Objects pointer/store
certificate. The whole delete code compiles the existing typed uint default,
loads/indexes the dynamic reference parent, then stores through the headerless
fixed-child index. No replacement compiler, evaluator or store semantics.

The combined theorem starts from INITIAL Source observer/MemOK/local alignment,
typed parent selection and scalar alignment, fixed bounds, local selected-address
separation and strong Objects representation. It derives the successful first
write's reached observer/MemOK/locals/parent lookup/representation, then uses
those outputs for actual deletion. Both independent Source statements, a single
Source Items execution, intrinsic Prog, separate prefix/suffix word runs and the
complete word append share the same actual heaps and machines. Original nps,
runtime n/indices/value and sufficient horizons h+6/h+5/h+7 are retained. The
first write uses the parent-index local as its child-index operand; this is the
explicit program's operand choice, not a Source-profile restriction.

Reached full Source correspondence and Objects representations, other objects
and Source addresses, parent references, locals/heap.next/world fields, saved
stack and any complete supplied allocator are derived. Repeated selected
identities remain supported; separation is only for distinct represented children,
not global injection. Valid bounds imply positive child length; no zero-length
fixed Source declaration admission is asserted.

The appended controls now construct a genuine populated strong input instead of
assuming one. Parent [LEFT,LEFT,RIGHT] is at word base16, fixed LEFT[7,0,max] at8,
fixed RIGHT[8,9,10] at24; four context slots, free cursor32 and stack[77,88] are
explicit. `nested_word_initial` proves Objects.StateRepr, complete AllocatorRepr,
actual Source correspondence and MemOK. `nested_word_program` instantiates both
original pipelines, records the full initial 16-word observation table and runs
the complete write/delete append: LEFT becomes[7,42,max] then[7,0,max], while the
parent and RIGHT are retained. Both reached full Objects relations and Source
observers/MemOK, final complete allocator and saved stack are proved. Existing
complete Source tables/locals/world/failure vectors remain intact. Explicit raw
16-word intermediate/final projections were not part of this checkpoint; they
are now proved by `nested_word_tables` (see source-fixed-reference-word-tables.md).
A concrete late-revert word fixture remains pending.

All four new headline laws/clients have measured exact standard-axiom guards
[propext, Classical.choice, Quot.sound]. Actual failed controls are preserved:
an anonymous Word constructor parse failed, fixed with explicit Word.val, and an
opaque State.heap rewrite failed, fixed by exposing that projection. No expected
observation, premise or budget changed. Independent source and committed artifact
reviews are recorded with delivery.

Symbolic word execution is not physical-byte or external compiler/EVM adequacy.
Full original gates, G32/P6b/G34/G35.02 reference remainder/G35.03 and both
Backfills remain partial. G33 and G35.01/.04/.05/.06 remain delegated/open.
Original goal identity/status remain unchanged BLOCKED; no publication claim.
