---
paths:
  - "Solidity/Typing/*.lean"
  - "Solidity/Semantics/*.lean"
---

# Typing and the interpreter

The typed syntax is what well-typedness was: a statement no rule can run
cannot be written, so no theorem of the calculus carries a typing hypothesis.
What is left here is about *values*: `Typing/Storage.lean` (`SVal.hasTy`, the
runtime sorts), `Typing/StoragePreservation.lean` (writes keep a value's
type), `Typing/State.lean` (`StateWT`, the full-state invariant).

`Typing/Soundness.lean` proves the interpreter keeps the invariant
(`Stmt.run_wt`, over a locals context `Stmt.wt` threads), and
`Typing/Reachability.lean` that every reachable storage is canonical
(`reachable_canon`). `SortCheck/Faithfulness.lean` uses both: a taclet's
declared read sort holds of what a well-typed run reads.

`Typing/Constructibility.lean` is the converse: canonical and tight
(`SVal.tight`) is exactly reachable (`reachable_iff`, for `Ty.okDeep`
roots), by a typed builder that reaches past an array's end through aliases
`slot d`. A new statement needs its case in `Stmt.run_tight` beside
`Stmt.run_canon`.

`Semantics/Agree.lean` is the frame kit every soundness proof composes:
`EnvAgreeExcept ns`, and a `*_frame` lemma per evaluator. A new evaluator in
`Semantics.lean` needs its frame lemma there.

Interpreter changes that follow solc over KeY are recorded in
`docs/solc-alignment.md`.
