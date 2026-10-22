---
paths:
  - "Solidity/Examples/**/*.lean"
  - "Solidity/Theory/**/*.lean"
  - "Solidity/Update.lean"
  - "Solidity/Calculus/Notation.lean"
  - "Solidity/Calculus/SurfaceNotation.lean"
---

# Examples and the notation

Two directories, by proof style:

- `Examples/Chains/` — the calculus's worked examples, one file per section in
  its order (`~/projects/Pre-licenciate-paper/sections/*.tex`), each one chain
  term in the printed fresh names (a `FreshNames` table per example where
  the trace renames a capture). Only those examples go there, once each.
  The convention:
  1. **One chain term, every line written.** A worked chain is
     `theorem chain : A ~[r]~> B ~*> C ~[findOnSave]~> D … := by sol_chain`
     over a scoped line (`dl![m]{ … }` on `Post`): `Fml.Via`, past the
     program too (`Calculus/ChainKit.lean`), propositions. No `calc`, no `_` line,
     the statement shows the whole trace. Every worked chain reads the scoped
     calculus; `φ : Post C Γ` stands at the context of the line's user
     locals (the fresh ones, a rule's or the elaborator's captures, dropped).
     `~~>` (`Fml.Leads`, `Fml.LeadsK` to a written last line) and `calc`
     are the notation's (`ChainNotation`), not a worked chain's. (A lone
     `~*>` is the derivation itself, data: a `def`.)
  2. **No binding is dropped.** No `~[simplifyUpdate]~>`: the fresh captures
     (`se1`, `sp1`, `pv`, `acc`, …) stay in the update to the last line.
  3. **To the last step.** Past the program the stack merges
     (`~[sequentialToParallel]~>`) and every read is resolved by its laws,
     until no rewrite but `simplifyUpdate` applies. `#last_line chain`
     (`Calculus/LastLine.lean`) follows every chain and is silent exactly
     there; otherwise it says which rewrite still applies and what it gives.
  4. **One link per rewrite**: `~[findMemberCons]~>`,
     `~[selectOnSaveMember]~>`, `~[selectOnDelAtMember]~>`,
     `~[findOnSave]~>`, `~[findOnDelAtBelow]~>`, `~[readOnWrite]~>`, a literal
     folded, … each with its line. No `sol_rws [..]` link in a chain. A
     premise a law needs is a hypothesis of the chain (`st!{ … }`,
     `pt!{ … }`); a member name alone (`age`, `account.balance`) is a path in
     the frame of a `select`.
  5. **Strategy steps as the paper prints them.** A run the paper prints as
     `⇝*` is one `~*>`; a step it prints as `⇝` is its own `~[rule]~>`, or
     one `~*>` where Lean takes several rules for it (an alias bound and read,
     a capture and its binding).  `#chain` groups the steps
     (`Chain.groupSteps`): declarations dropped with the bindings they
     leave are one `~*>`, and so is a rule with the `emptyModality` after it
     (the paper never shows the `⟨[ ]⟩` line).  The paper's grouping wins over
     `#chain`'s: where it folds more, join links into one `~*>`; where it
     prints a step `#chain` folded (a declaration dropped, `⇝`, before the
     `⇝*` that binds it), split it out as its own `~[rule]~>`.
  6. **Concrete values.** The program stays the paper's; the first line puts
     a concrete starting state in front of it as an update, and gives each
     free parameter (`ageVal`, `v`, `i`, …) a small distinct int there:
     `dl![m]{ { ageVal := 42 ‖ storage := save(storage, alice.account.balance, 10) } ⟨[ … ]⟩ φ }`,
     so every read resolves to a literal and arithmetic folds at the last
     line.  Where the section itself states a concrete postcondition (`x = 9`,
     `Examples/Chains/FixedLength.lean`), the chain keeps it, its program
     reads no free parameter, and it runs to `true`.
  7. **Fast.** A file checks in the time it did before or faster, and no
     chain is given a bigger `maxHeartbeats`. A scoped chain is one
     declaration however long (`Storage.BalanceWriteRead` has 13 links,
     `MemoryDelete.IndexedDelete` more).

  Generate a chain with `#chain φ` (the `chain-authoring` skill) rather than
  writing it line by line: it prints the statement in this form. A read of
  the state as the program found it (`find(storage, p)`) is a last line.

  For a document needing separate source/receiver/index captures, import
  `Solidity.Tools.ProgramTrace` and use `#latex_program` or its JSON export
  (`docs/latex.md`). Disabling grouping alone does not split `CaptureAll`.
  The checked relation is `Fml.Leads`; the final leaf still needs a proof,
  and other native rules retain their own granularity.
- `Examples/Tactics/` — formulas `⊨ᶠ dl!{ pre → [ program ] post }` proved by
  tactics, and interpreter runs.

The notation's own tests (`ChainNotation`, `ChainRewrites`, `ExampleNames`,
`Notation`, `ProofTree`, `Tools`, `Verify`) stay at the root. A program is
shown once per style: before adding one, `rg` for it.

A tactic example is over a named contract
(`local instance : InContract := ⟨StandardExample⟩`), under
`open scoped Solidity.Scoped`, so `dl!{ … }` is a scoped `Fml C []`; proved
one of two ways:

- **by the strategy**: `sol_symex` fires the one rule each statement has,
  `sol_close` finishes the first-order goal in an arbitrary state;
- **by a walk**, for a worked example: `apply Proves.fmlValid`, then
  one `apply` per taclet (`unfold r`, `update r`, `split r`, `Proves.check r`,
  `done r`, `empty`, `intro`; `Calculus/WalkSyntax.lean`), and
  `sol_leaf; sol_close` at each leaf. Each rule the walk takes is named
  in the proof, so renaming a rule breaks the example. `sol_derive?` writes
  the walk out (`Calculus/Derive.lean`), as `#chain` writes a chain.

Every theorem has a docstring with its Solidity. Every file has its own
namespace `Solidity.Examples.<Dir>.<File>`: an anonymous `local instance` gets a
generated name, and two files in one namespace clash when both are imported.

**Do not spell a formula out as raw constructors.** If `dl!{ … }` cannot say
something, extend the notation (`Calculus/SurfaceNotation.lean`, its scoped
reading `Calculus/Notation.lean`); if a goal prints with a `‹…›` escape,
extend the printer (`Calculus/RuleSyntax.lean`, `Calculus/Delab.lean`).

**Fml.Valid means every typed state** (`Fml.Valid`, `Calculus/Logic.lean`): a typed
storage has every member, so a write under the diamond along a path through
no array slot returns and its leaf closes (`⟨ alice.age = 1; ⟩ true`,
pinned in `Examples/ProofTree.lean`). A write at an index, or through the
alias a `push()` returns, may revert: write the box, or state the
precondition. A claim about the contract's initial store is a typed run
(`Prog.runT` from `State.exampleStore`, `Tools/Run.lean`), pinned
with `#guard_msgs in #eval`.

When `sol_close` does not close a true goal, the gap belongs in
`Calculus/Close.lean` (its docstring lists what it cannot do yet), not in a
bespoke proof in the example.
