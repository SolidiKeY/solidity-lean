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

The execution-level theorems — the interpreter keeps `StateWT`, and its
tightness (`reachable ⇒ canonical`) — were stated over the untyped
interpreter and are to be ported over `Stmt.run` (`docs/kernel-port.md`,
"Port later"). Until then nothing may assume them.

`Semantics/Agree.lean` is the frame kit every soundness proof composes:
`EnvAgreeExcept ns`, and a `*_frame` lemma per evaluator. A new evaluator in
`Semantics.lean` needs its frame lemma there.

Interpreter changes that follow solc over KeY are recorded in
`docs/solc-alignment.md`.
