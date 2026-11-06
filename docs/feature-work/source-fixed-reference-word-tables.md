# Exact nested word tables

`SourceUintFixedRefsExact.lean` proves `nested_fixed_store_exact`: the actual
published value/pointer/parent-index/read/fixed-index/store append executes to
`writeMachine m (base child + index) value`. Inputs are INITIAL Objects.StateRepr,
local/root alignment, actual selected child, valid fixed index, a fragment-valid
typed value and its initial typed evaluation to the supplied uint word. No final
machine, whole-program successful run or preservation equality is a premise.
The value/path/index runs and single store effect derive from published val_sim,
PtrFrag.run_of_eval and ArrayRepr.write. The array failure alternative contradicts
the initial bound. No evaluator/compiler/heap representation is replaced.

The generic statement permits every runtime fixed length/index and uint word
compatible with these existing initial representation/fragment premises. It adds
no Source admission cap or zero-length fixed declaration admission. The exact
cell update additionally frames unrepresented padding, which the reached Objects
relation alone would not determine. This is a word-machine result, not an
Environment byte-memory or external compiler/EVM theorem.

`nested_word_tables` calls the existing actual Source Items/whole-word write-delete
producer in BOTH pipelines. Execution determinism identifies its actual prefix
and final machines with the derived updates of cell9: write42 then write0.
The complete ordered observation addresses are
[0,1,2,3,4,8,9,10,11,16,17,18,19,24,25,26]. Initial values are
[32,16,42,1,1,7,0,max,0,3,8,8,24,8,9,10]; prefix values replace only the seventh
entry (cell9) with42; final values equal the initial table. No entry is dropped:
free cursor, all four locals, every parent/child/neighbour word and padding11
are included. Prefix table inequality discriminates skipping the actual write.
The Source execution, both reached Source observers/Objects representations,
final complete allocator and both saved stacks[77,88] remain linked to those
same actual machine outputs. Prior complete Source tables, frames and failures
are unchanged; error rollback is not asserted.

The new producer/client have measured exact standard-axiom guards
[propext, Classical.choice, Quot.sound]. Initial focused checks passed on their
first attempts, with historical raw failures and seals preserved. Independent
read-only source/control and committed-artifact reviews are recorded in delivery.
No heartbeat, fuel, node, test or wall-time budget was raised; exact component
certificates avoid monolithic instruction-program normalization.

The concrete late-revert word fixture is now supplied by nested_word_late_tables
(see source-fixed-reference-word-late-fixture.md). Physical bytes, general construction/failure,
full original gates and final Source/V10/target/world/compiler adequacy remain
open. G32/P6b/G34/G35.02 reference remainder/G35.03/Backfills A/B are partial;
G33 and G35.01/.04/.05/.06 remain delegated/open. Goal remains unchanged BLOCKED.
