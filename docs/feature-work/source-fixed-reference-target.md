# Nested fixed-child target assignment

`SourceUintFixedRefsTarget.lean` adds `uintFixedChildPath`, selecting a fixed uint
child from a dynamic reference parent, and `uintFixedChildWriteCode`, the complete
existing value-load/pointer-load/parent-index/read/fixed-index/store word append.
`SourceUintFixedRefsAt.resolved_write_word` joins the actual nested Source
assignment/statement to an actual intrinsic assignment and whole `Evm.run` result.
It consumes the existing `Objects.PtrFrag.index`/`write` certificates, not a new
compiler, evaluator or store semantics. The code is built from the published
`compileVal`, `Objects.readCode` and `Objects.writeCode` operations.

Inputs are INITIAL Source observer/MemOK, Source and target scalar/root alignment,
actual selected typed child, runtime fixed bounds, the existing local selected
Source-address separation and full `Objects.StateRepr`. There is no desired
postrun, final representation or unrelated second successful execution premise.
The actual Source and typed write select one shared output heap, and the word
certificate derives the reached strong representation. Source locals/heap.next,
parent/other typed objects, other Source addresses and all world fields are
framed; target saved stack and any complete supplied allocator are preserved.
The Source assignment remains RHS-first at horizon+4; statement horizon+5 uses
explicit nps. Generic runtime parent length/index/fixed length/value are retained,
without a new public shape, depth or fuel admission bound.

The appended `nested_typed_program` client inhabits actual Source Items and
intrinsic Prog over the same changed prefix and final heap. It reuses the full
previous `nested_mutation_delete` observations: [LEFT,LEFT,RIGHT], LEFT changes
[7,0,max] to [7,42,max] then [7,0,max], RIGHT remains [8,9,10]. It derives the two
intrinsic statements from those actual Source-produced writes and parent frame,
then uses the published intrinsic pair runner. All prior complete Source tables,
world/local/alias/bounds/timeout/type/empty-parent observations remain unchanged.
This client does not yet instantiate the full Objects/word-machine premises of
the generic theorem. A populated whole-word fixture and nested write/delete word
append, target bounds cases and physical-byte execution remain pending.

The new generic law and client have exact measured standard-axiom guards
[propext, Classical.choice, Quot.sound]. Three failed client attempts are retained:
output-type inference and opaque statement runner, then explicit path/heap
projection issues. Explicit typed path evaluations and State.heap projections
repair these without changing the statements, premises or proof budgets.
Independent read-only source and artifact reviews are recorded in delivery.

No Source-to-bytecode/compiler/EVM, external execution, general allocation failure
or whole-lane adequacy follows. Full original gates and G32/P6b/G34/G35.02 reference
remainder/G35.03/Backfill A/B stay partial; G33 and G35.01/.04/.05/.06 remain
delegated/open. The original goal remains unchanged BLOCKED.
