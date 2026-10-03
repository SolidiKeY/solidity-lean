---
paths:
  - "Solidity/Examples/**/*.lean"
  - "Solidity/Theory/*.lean"
  - "Solidity/Update.lean"
  - "Solidity/Calculus/Notation.lean"
---

# Examples and the notation

Two directories, by proof style:

- `Examples/Chains/` — the calculus's worked examples, one file per section in
  its order, each a chain (`calc` of `dl![m]{ … }` lines, `~[r]~>` for a
  printed `⇝`, `~*>` for a `⇝*`) in the printed fresh names (a `FreshNames`
  table per example). Only those examples go there, once each. A written
  line binds an alias to its path as the printed line does: a line of the
  strategy that binds an alias through another alias (`{ tokRef := bobAcc.token }`),
  indexes by a capture (`sp[idx]`) or binds a callee's local is crossed
  unwritten (`_ ~> _ := by sol_chain`, one per step, or `_ ~*> _` to the end
  of the program), the next written line being its `~[sequentialToParallel]~>`.
  A read the printed trace resolves is resolved by its own link, in the
  update's right-hand side, a member at a time as solkey reads it
  (`~[findMemberCons]~>`, `~[selectOnSaveMember]~>`, `~[selectOnDelAtMember]~>`,
  then `~[findOnSave]~>` or `~[findOnDelAtBelow]~>`), the premise it needs a
  hypothesis of the chain written with `st!{ … }` and `pt!{ … }`; a member
  name alone (`age`, `account.balance`) is a path in the frame of a `select`.
  A copy read back goes through the laws of memory reads
  (`~[findCopyMem]~>` then `~[readOnWrite]~>`; `~[readCopySt]~>` then
  `~[findOnSave]~>`), after one `~[sequentialToParallel]~>` that merges the
  memory write and the locals beside it into the update after.
  **Every chain ends at one parallel update**: past the program the stack
  merges (`~[sequentialToParallel]~>`), each read is resolved by its law, and
  the fresh captures that cannot halt and nothing reads go in a last
  `~[simplifyUpdate]~>` (a user local stays; `pv := x + 2` stays, it may halt).
  `#last_line chain` (`Calculus/LastLine.lean`) follows every chain that is a
  whole trace, not a segment composed into one: it is silent at a last line
  and otherwise says which rewrite still applies and what it gives — the
  worklist for the line to write next. A read of the state as the program
  found it (`find(storage, p)`) is a last line. A `FreshNames` table is
  written only where the printed trace renames a capture; the elaborator's
  own `se1`, `sp1` need none. A chain over ten updates is split into
  segments composed in a `calc`, never given a bigger `maxHeartbeats`.
- `Examples/Tactics/` — formulas `⊨ dl!{ pre → [ program ] post }` proved by
  tactics, and interpreter runs.

The notation's own tests (`ChainNotation`, `ChainRewrites`, `ExampleNames`,
`Notation`, `ProofTree`, `Tools`, `Verify`) stay at the root. A program is
shown once per style: before adding one, `rg` for it.

A tactic example is over a named contract
(`local instance : InContract := ⟨StandardExample⟩`), proved one of two ways:

- **by the strategy**: `sol_symex` fires the one rule each statement has,
  `sol_close` finishes the first-order goal in an arbitrary state;
- **by a walk**, for a worked example: `apply Proves.valid`, then
  one `apply` per taclet (`unfold r`, `update r`, `split r`, `done r`,
  `empty`, `intro`), and `apply close; sol_close` at the end. Each rule the
  walk takes is named in the proof, so renaming a rule breaks the example.
  `sol_derive?` writes the walk out (`Calculus/ProofTree.lean`), as
  `sol_chain?` writes a chain's `calc`.

Every theorem has a docstring with its Solidity. Every file has its own
namespace `Solidity.Examples.<Dir>.<File>`: an anonymous `local instance` gets a
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
