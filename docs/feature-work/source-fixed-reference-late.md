# Nested fixed-child late target failure

`SourceUintFixedRefsLate.lean` composes the existing actual nested fixed-child
assignment with the existing bounds producer. `resolved_write_late_bounds_word`
starts from initial Source observer/MemOK, Source/target local/root alignment,
actual typed parent selection, local selected-address separation, initial strong
Objects representation, a valid first child index and invalid second child index.
It executes a first write using the parent-index local as the child-index operand,
then an assignment using the separate bad child-index local. These are the actual
program operands, not a restriction on the admitted Source profile.

The second Source observer, unchanged locals, typed parent lookup and Objects
representation derive from the actual first write. No reached representation,
second run or desired postcondition is a premise. Both original Source nps and
runtime fixed length/index/value are retained. Sufficient horizons are first
statement h+6, second statement h+5, Items h+7; no minimal-fuel or admission cap.

Conclusions link all three existing executions: the successful Source statement
and rejecting expression/Items; successful intrinsic assignment then failing
assignment/Prog; successful complete word code producing mm, rejecting complete
suffix on mm, and the complete appended code reverting. The theorem exposes the
actual prefix heap, Source state, machine, strong Objects relation, Source MemOK,
locals/heap.next, unchanged parent/other typed objects/other Source addresses,
world fields, saved word stack and any complete supplied allocator frame.

Source Items error returns `.nil` plus reached globals ym.2. Prefix locals ym.1
and their equality to initial locals are separately witnessed by the prefix run.
Intrinsic/word errors return no state or panic bytes. No post-revert machine,
transaction rollback, or Source-payload/target-payload equality is inferred.

The inhabited `nested_late_program` control in both original pipelines derives
an actual intrinsic successful prefix and failing Prog from the same actual
Source-produced heap. Parent [LEFT,LEFT,RIGHT], LEFT [7,0,max] changes to
[7,42,max], RIGHT [8,9,10] remains; endpoint3 rejects at length3. Full Source
prefix object/local/world/heap-bound vectors are retained from the earlier
late-endpoint client, together with its changed-versus-initial discriminator.
The new generic word theorem is proved under its explicit strong representation;
a populated concrete word-machine instantiation remains pending.

The producer and new client have measured exact standard-axiom guards
[propext, Classical.choice, Quot.sound]. The first client attempt failed because
`prefix` is a Lean reserved keyword; renaming only that local proof binding fixes
it. Raw failure and repaired receipts are preserved. Independent read-only source
and committed-artifact reviews are recorded in delivery.

Physical byte execution, concrete word fixtures, full original gates and final
Source/V10/target/world/compiler/EVM adequacy remain open. G32/P6b/G34/G35.02
reference remainder/G35.03/Backfills A/B stay partial; G33 and G35.01/.04/.05/.06
remain delegated/open. Original goal identity/status remain unchanged BLOCKED.
