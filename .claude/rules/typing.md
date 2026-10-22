---
paths:
  - "Solidity/Typing/*.lean"
  - "Solidity/Semantics/*.lean"
---

# Typing and the interpreter

The typed syntax is what well-typedness was: a statement no rule can run
cannot be written, so no theorem of the calculus carries a typing hypothesis.
The typed state is what a well-typed state was: its storage holds the
contract's roots at their types, its heap objects at the types its typing
lists.  What is left here is about what the types do not say, read on the
typed state only.

Each run invariant is a hereditary predicate on typed values
(`Typing/Values.lean`: `SVal.All P` for node conditions `P : Hered`):
canonical (`canonH`, `Typing/Reachability.lean`), tight (`tightH`,
`Typing/Tight.lean`) and bounded (`bndH`, `Typing/Fits.lean`).  The typed
run keeps each one statement by statement, once for all three
(`Stmt.keeps_all`, `Typing/HeredRun.lean`): a predicate states its node
conditions' preservation by each storage operation (`HeredRun`) and the
leaves follow.  A new statement needs its leaf in `Stmt.keeps_all` (against
its typed step `TRun.*`, `RunInv.TKeeps`, `Typing/TypedRunInv.lean`) and in
`Stmt.asserts`/`Stmt.run_noPanic` (`Semantics/NoPanic.lean`); a new storage
operation needs a field of `HeredRun` (or a lemma from its fields).

`Typing/Constructibility.lean` is the converse: canonical and tight is
exactly reachable for a storage whose keys and slots fit (`reachable_iff`,
for `Ty.okDeep` roots, under `SVal.Fits`; implied under `FixedFits`,
`reachable_fits`, so `reachable_iff_fits` has no premise on the storage;
decisions 77 and 97 of `docs/intrinsic.md`), by a builder that reaches past
an array's end through aliases `slot d` (`Build.fill`, `fill_ok`).

The run is `Semantics/Run.lean`'s, over typed states; there is no untyped
state (W10.5.6).  `Typing/CanonTest.lean` proves what the tests of
`wt(storage)` decide; the tests themselves are folds low in the stack
(`Semantics/StorageWt.lean`), since the term `wt(storage)` runs them
(`Storage.wtT`, `Signature.lean`) and the kernel evaluates them in
certificates.

Changes to the run that follow solc over KeY are recorded in
`docs/solc-alignment.md`.

Contract-specific transaction reachability is `Semantics/Lifetime.lean`
(`docs/lifetime.md`): successful constructor first, then an explicit interface.
Keep it distinct from `Typing/Reachability.lean`'s arbitrary-program storage
constructibility and `ReachableBy`'s storage-only preservation. Its commits need
actual successful runs; exhaustion and callback havoc are not witnesses.
