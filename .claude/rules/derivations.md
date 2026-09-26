---
paths:
  - "Solidity/Examples/*.lean"
  - "Solidity/Theory/*.lean"
  - "Solidity/Update.lean"
  - "Solidity/Calculus/Notation.lean"
---

# Examples and the notation

An example is written as the calculus writes it: a formula in its
notation, `⊨ dl!{ pre → [ program ] post }`, over a named contract
(`local instance : InContract := ⟨StandardExample⟩`). It is proved one of two
ways:

- **by the strategy**: `sol_symex` fires the one rule each statement has,
  `sol_close` finishes the first-order goal in an arbitrary state;
- **by a walk**, for a worked example: `apply Proves.valid`, then
  one `apply` per taclet (`unfold r`, `update r`, `split r`, `done r`,
  `empty`, `intro`), and `apply close; sol_close` at the end. Each rule the
  walk takes is named in the proof, so renaming a rule breaks the example.

Every theorem has a docstring with its Solidity. Every file has its own
namespace `Solidity.Examples.<File>`: an anonymous `local instance` gets a
generated name, and two files in one namespace clash when both are imported.

**Do not spell a formula out as raw constructors.** If `dl!{ … }` cannot say
something, extend the notation (`Calculus/Notation.lean`); if a goal prints
with a `‹…›` escape, extend the printer (`Calculus/RuleSyntax.lean`).

**Valid means every state.** `⊨` quantifies over every state, including
ones without the contract's roots, so a write under the diamond is not valid
(`⟨ alice.age = 1; ⟩ true` fails where `alice` is missing). Write the box, or
state the precondition. A claim about the contract's initial store is a run
of the interpreter from `State.exampleStore`, checked by `rfl` or pinned with
`#guard_msgs in #eval` where `rfl` cannot unfold a struct default.

When `sol_close` does not close a true goal, the gap belongs in
`Calculus/Close.lean` (its docstring lists what it cannot do yet), not in a
bespoke proof in the example.

