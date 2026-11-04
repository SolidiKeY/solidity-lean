# Computed reference replacement followed by reached deletion

`Solidity.Backend.MemoryOps.SourceBoolRefsAt.computed_reference_delete_sequence`
in module `SourceReferenceReadSequence` derives one existing
Source `RItems`, intrinsic `Prog`, and whole symbolic-word append execution.
INITIAL source-parent contents compute `src[j]`; actual replacement installs it
in `dst[i]`. The second nested delete resolves that reached pointer. Its bounds,
observer, MemOK, full RefArrayStateRepr, operand alignment and allocator are
derived from the first output, not independent successful runs/postconditions.

Premises: initial destination/source finite Boolean-child parent observers;
root/index local alignment; parent bounds; selected child's initial inner bound;
Source MemOK; full RefArrayStateRepr. Distinct INITIAL destination descendants
need only separate Source addresses from this selected child. This is a local
sufficient observer condition, not global address injection or an admission
restriction. StructAllocatorRepr transport retains its positive-base and initial
live-parent/cursor bound. Parent aliases and repeated/shared children are allowed.
Source horizons are fuel+6, fuel+5, combined fuel+7 with ORIGINAL Γ.length nps.
No minimum-fuel or arbitrary side-effectful RHS/LHS-order theorem is claimed.

Controls in SourceReferenceReadControls reuse its unchanged populated fixture.
For both pipelines and distinct/same parents, src[1]=RIGHT is computed, parent[0]
is redirected, then RIGHT[1] changes true to false. LEFT and all parent identities
remain. All five Source/native objects and all 24 represented word cells are
ordered INITIAL/intermediate/final observations; locals/world/next, guard, empty
parent, header/content, saved stack and allocator are retained. Vector negatives
compare omitted deletion and a stale write without rebinding. They are not an
executed reversed two-statement program. Prior standalone endpoint and timeout
controls remain unchanged; a new late-rejection composition is not claimed here.

Measured exact standard axiom sets: generic/client [propext, Classical.choice,
Quot.sound]; complete-vector control [propext]. Focused diagnostics and affected
closure are recorded in the immutable checkpoint evidence. Actual failed draft
checks are retained. No Source/Evm producer edited, new semantics/axiom/sorry,
raised budget, constructor/copy/ABI/byte/EVM/compiler adequacy claim follows.
Full private lane/default/TestSuite/strict/corpus closure remains pending (prior
literal toolkit Python127 and cold-library124 boundaries retained); per-module
checks are not relabeled full gates. Raw global docs/inventory failures remain
separate from complete public zero-new comparison. All original parents and
Backfills remain partial/delegated/blocked as recorded in the checkpoint handoff.
