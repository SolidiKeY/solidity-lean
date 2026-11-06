# Reached alias, write and same-index deletion

Module `Solidity.Backend.MemoryOps.SourceUintAliasWriteDelete` adds
`Solidity.Backend.MemoryOps.source_uint_delete_objects_word`, a strong numeric
delete adapter over actual Source write/delete semantics, intrinsic primitive
delete/default-write identity and existing Objects pointer/value certificates.
No compiler, allocator, heap, Source evaluator or intrinsic representation is
replaced. The final strong representation is derived, rather than supplied.

`Solidity.Backend.MemoryOps.source_uint_alias_write_delete_word` consumes
INITIAL Source/local/native scalar and pointer alignment, SourceUintMemoryAt,
Source MemOK, actual selected bounds, strong Objects StateRepr/AllocatorRepr,
positive base and index/RHS valIn. Existing alias/write execution supplies the
SAME selected reference, updated contents, unchanged operands and strong frames
for deletion. The first write's set/length laws derive the reached value and
third-operation bound. No intermediate observer/run or final agreement is a
premise. Runtime lengths and canonical uint256 values remain quantified.

The conclusion contains actual Source expressions and ONE three-statement
RItems execution with original parameter count; ONE intrinsic Prog; actual
prefix and suffix word executions and the WHOLE existing code append. Source
expression horizons h+5/h+4/h+3 and Items h+7 are sufficient, not minimal-fuel
or public admission claims. Final MemOK, Source/native content relation,
strong Objects/allocator, stack/free pointer and other object/address/local/
world/ex/events/logs/fnLocals frames follow those actual outputs. The third
operation uses the same index, so its valid bound follows unchanged length;
this supported component is not a restriction on admitted source programs.

Additive controls in SourceUintReadAssignmentControls instantiate both original
pipelines and distinct/self alias identities. They derive concrete outputs by
execution determinism and retain complete initial/alias/written/deleted twenty-
word vectors, Source/native object tables, locals/world/caller frames, allocator
and saved stack. Distinct selection gives9->42->0; self gives0->42->0 while old
aliases/unrelated objects are framed as appropriate. Source reads prove42 in
the reached prefix and0 after deletion. Final words equal direct deletion;
that equality is explicit, so skipped-write discrimination uses the ordered
prefix, not a false final-state difference. Source Items at horizon6 retain
the actual written42 heap before deletion times out. The failed outcome only
exposes globals; prefix locals are proved separately. No target timeout,
post-revert machine, rollback or panic-payload equivalence is invented.

Prior controls/vectors/guards are byte-preserved. Exact headline axiom guards
remain standard-only. Kernel/symbolic-word checking is separate from external
solc/EVM/physical-byte correctness. Full private wrapper/TestSuite/strict/corpus,
raw docs/inventory failures and final Source/V10/world/representation/copy
producers remain open. No new cold timing coverage, source exclusion, changed
budget, other-owner edit or whole-lane completion follows from this component.
