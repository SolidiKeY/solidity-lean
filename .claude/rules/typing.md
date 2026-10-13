---
paths:
  - "Solidity/Typing/*.lean"
  - "Solidity/Semantics/*.lean"
---

# Typing and the interpreter

The typed syntax is what well-typedness was: a statement no rule can run
cannot be written, so no theorem of the calculus carries a typing hypothesis.
What is left here is about *values*: `Typing/Storage.lean` (`SVal.hasTy`, the
runtime sorts), `Typing/StoragePreservation.lean` (what the erased
operations produce is typed: a fresh default, arithmetic ints, lengths,
nodup lookups), `Typing/State.lean` (`StateWT`, the invariant of a state's
global part; `LTy.WT` in `Typing/Soundness.lean` types a local).

`Typing/TypedWT.lean` shows a typed state's erasure is well-typed by
construction (`State.glob_wt`); `Typing/Soundness.lean` gives the shape of
a run invariant (`RunInv`); and `Typing/Reachability.lean` that every reachable storage is canonical
(`reachable_canon`). `SortCheck/Faithfulness.lean` uses both: a taclet's
declared read sort holds of what a well-typed run reads.

`Typing/Constructibility.lean` is the converse: canonical and tight
(`SVal.tight`) is exactly reachable for a storage whose words, keys and
slots fit (`reachable_iff`, for `Ty.okDeep` roots, under `FitsStorage`; not
implied by `Reachable` in general (`huge_reachable_not_fits`), implied under
`FixedFits` (`reachable_fits`; `reachable_iff_fits` drops the premise),
`Typing/Fits.lean`, decisions 77 and 97 of `docs/intrinsic.md`), by a typed builder that reaches past an array's end through aliases
`slot d`. A new statement needs its cases in `Stmt.keeps_canon`
(Reachability), `Stmt.keeps_tight` (Constructibility) and `Stmt.keeps_fits`
(Fits), each leaf against its typed step `TRun.*` (`RunInv.TKeeps`,
`Typing/TypedRunInv.lean`), and in
`Stmt.asserts`/`Stmt.run_noPanic` (`Semantics/NoPanic.lean`).

The run is `Semantics/Run.lean`'s, over typed states; `Semantics.lean` keeps
the untyped state's operations, which the typed ones erase to
(`Semantics/StorageErase.lean`, `HeapErase.lean`, `Semantics/Erase.lean`,
`TypedErase.lean`) for the Typing chain (the EVM reads the typed state,
W10.5.3, and the memory laws the typed heap, W10.5.4); the
typed core (`State`, `Heap`, `Run`, `Signature.lean`) imports none of them
(W10.5.1).

Changes to the run that follow solc over KeY are recorded in
`docs/solc-alignment.md`.
