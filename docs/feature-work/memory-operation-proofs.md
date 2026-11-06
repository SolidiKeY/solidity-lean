# Source, heap and word memory-operation proofs

`Backend/MemoryOps/` connects selected existing Source evaluations to intrinsic
heap operations and the abstract word machine. It contains typed representations
and transports for primitive/calldata values, arrays and child aliases; memory
allocation/defaults, reads, assignments and deletion; and bounded operation
composition. Each module retains its stated resolution, initial representation,
heap shape, bounds, capacity and arithmetic premises. These are proof components,
not an admission change or a completed compiler theorem.

## Reached decrement failure and timing

`SourceUintFixedDecrementLate.lean` derives a successful first `1 → 0` write,
then applies the second checked decrement to that reached state. Source failure
retains the reached heap and world observations. The intrinsic program and
abstract word program revert; the word result exposes no suffix machine.
`SourceUintFixedDecrementLateTiming.lean` separately derives a successful prefix
followed by a Source horizon timeout. Neither result asserts outer transaction
rollback or identifies Source fuel with physical EVM gas.

`SourceUintFixedDecrementBounds.lean` proves that an invalid fixed-array index
fails before a read, arithmetic or write. Its controls retain an inhabited valid
write as well as invalid-index and stale-initial-state negative checks.

The two control modules quantify over the represented pipeline and prefix/postfix
choices, retain distinct populated heap objects and aliases, and observe the
caller stack tail, allocator, selected and unselected cells, Source exception,
events, logs and saved function frame. These are executions of the existing
Source/intrinsic/word operations, not detached arithmetic examples.

## Recovery and review

The 85 dependency modules are preserved byte-for-byte from original V11 commit
`e11335bb3405fe44e9cfe83af960e732d21e76a2`. The five decrement modules originate
in its checksum-bound C75/C76 RAM drafts. Local integration retains current
master's core semantics, including its later Panic decoder and type-spelling
repairs; it does not overwrite those files with the producer snapshot.

Confirmed control-proof failures were repaired with the existing
`MObj.elems_fixed` law before concrete reduction and heap-vector rewriting.
Intermediate facts have explicit types; indexed-list bounds are supplied
explicitly to avoid expensive implicit search under the unchanged heartbeat
limit. A measured standard-axiom report was corrected after its body checked.
No theorem statement, input premise, observation vector or negative expectation
was weakened, and no axiom, unsafe evaluator or larger proof budget was added.
Original failed drafts, diagnostics and source hashes are preserved separately.

## Remaining boundary

The physical byte layout/allocator, fetched compiled EVM execution, arbitrary
callee/world agreement, full source admission/lowering, production coverage and
final backend composition remain separate obligations. This checkpoint does
not close V11, G32–G35 or any whole-lane assignment. Existing frontend refusals,
profiles, public expected verdicts and resource limits remain unchanged.

All 90 components pass the combined core build, SolKey TestSuite and retained
`473da8944c` annotation check with cache reuse. The final run took about ten
seconds and peaked at 1.07 GiB under the hard 12 GiB/no-swap cap and monitored
12 GiB host reserve. All five new modules have clean per-file diagnostics.
Finder and skeptic reviews confirmed the selected statements and scope.

Trust, layer, orphan and whitespace gates pass. All 567 added axiom pins are
standard-only. Global axiom and documentation checks retain the exact committed
baseline's 410 and 86 findings respectively, with none added. Raw failures,
comparison results, source hashes and gate receipts are preserved; these
comparisons do not assert clean global inventories.
