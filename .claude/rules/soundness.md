---
paths:
  - "Solidity/Calculus/Sound*.lean"
  - "Solidity/Calculus/RuleSoundness.lean"
  - "Solidity/Calculus/Logic.lean"
  - "Solidity/Calculus/Symex.lean"
  - "Solidity/Calculus/Close.lean"
  - "Solidity/Counterexamples/*.lean"
---

# Soundness conventions

**The contract**: `Taclet.sound` proves every taclet's premise correct for its
statement (`Premise.Correct`), against `Stmt.run`, from every state, with no
hypothesis but that the rule's fresh names are fresh. `Proves.sound` and
`symex_sound` lift it to derivations. `#print axioms` on all three shows only
`propext`, `Classical.choice`, `Quot.sound`. Keep it that way: no `sorry`, no
new hypothesis.

## Proving a new case

- **Update premise** (`SoundUpdate.lean`): state a generic lemma
  `SameOk [] (Upd.apply [..] σ) (Stmt.run σ ..)` over the syntax pieces and
  close the case with `exact`. The update reads every right-hand side in the
  pre-state and the statement runs left to right; `upd_unfold` puts both into
  the same reads (`envVal`/`envRef` name the shared ones) and `res_split`
  splits both runs on them.
- **Unfold premise** (`SoundUnfold.lean`): the captured part is evaluated
  first, the fresh binding moves outward past every later read (the
  `*_setEnv` lemmas), and `agree_tac` closes the agreement off the fresh
  names. `SameOk` only asks both runs to halt, not to halt alike, so a premise
  may evaluate pure parts in another order.
- Develop a case as a standalone lemma in a scratch file; the whole theorem
  elaborates in about half a minute.

## When a case is false

Do not weaken the theorem. Find the state where the premise and the statement
end differently, check which one solc agrees with, and fix that side: the rule
(`Rules.lean`) or the interpreter (`Semantics.lean`, recording it in
`docs/solc-alignment.md`). `MSrc.mval` reading a memory reference through
`asRef` is such a fix: a copy from a slot holding a primitive refuted
`memoryFieldWriteCopy` until the interpreter read it as the rule does.
A refutation worth keeping goes in `Counterexamples/`, one file each.
