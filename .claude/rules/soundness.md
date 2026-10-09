---
paths:
  - "Solidity/Calculus/Sound*.lean"
  - "Solidity/Calculus/ProvesSound.lean"
  - "Solidity/Calculus/Logic.lean"
  - "Solidity/Calculus/Symex.lean"
  - "Solidity/Calculus/Close.lean"
  - "Solidity/Calculus/CloseErase.lean"
  - "Solidity/Counterexamples/*.lean"
---

# Soundness conventions

**The contract**: `Stmt.sound` (`Calculus/Sound.lean`) proves every rule
`Stmt.step` fires correct for its statement (`Stmt.Sound C`, from
`Premise.Sound`, `Calculus/ProvesSound.lean`), against the typed run
(`Stmt.run`, `Semantics/Run.lean`), in every typed state, at any fresh index,
with no hypothesis. A taclet is sound because its premise is the one
`Stmt.step` builds (`Taclet.toStep`, `Calculus/Taclet.lean`): there is no
proof per taclet. `Proves.sound`/`Proves.valid` and `symex_sound` lift it to
derivations; a leaf the closer proves is sound by its erasure
(`holds_of_erase_valid`, `Calculus/CloseErase.lean`). `#print axioms` on
them shows only `propext`, `Classical.choice`, `Quot.sound`. Keep it that
way: no `sorry`, no new hypothesis.

## Proving a new arm

- **The shape** (`Calculus/SoundKit.lean`): state what the premise asks of
  the statement's typed run (`Premise.Runs`); the premise kinds' lemmas
  (`Premise.sound_update` … `sound_done`) turn it into `Premise.Sound`. Name
  the arm's theorem `…_sound` and add it to `Stmt.stepSound_arms`
  (`Calculus/SoundStep.lean`), or to the blocks' (`SoundCalls`,
  `SoundLoops`).
- **Update premise** (`Calculus/SoundArms.lean`): an update is a term of
  `Update.lean`, read on the erasure, so state an equation between the
  update applied to an erased state and what the statement's typed step
  erases to (`*_run`, against `StepAgrees.erased` of its `TRun.x_erase`,
  `Semantics/StepErase.lean`), and close with `Premise.sound_update_erased`.
  A new typed step needs its erasure lemma first.
- **Unfold premise** (`Calculus/SoundCapture.lean`, `SoundLocal`, …): the
  fresh local is pushed and popped by the premise's frame; the runs compare
  up to the halt (`TRes.Sim`, `sound_unfoldSim`), the schema variables read
  under the fresh local by the shift lemmas (`Val.evalT_up` and kin).
- Under the diamond the typed run must not diverge where the update ends:
  an evaluator and every write but a push end (`Semantics/Ends.lean`); a
  push at the bound is `exhausted`, which both modalities accept.
- Develop an arm as a standalone lemma in a scratch module importing
  `Calculus/SoundKit.lean`; the arms' files elaborate in tens of seconds.

## When a case is false

Do not weaken the theorem. Find the state where the premise and the statement
end differently, check which one solc agrees with, and fix that side: the rule
(`Calculus/Rules.lean`, its arm) or the run (`Semantics/Run.lean`, recording
it in `docs/solc-alignment.md`). An unset memory local (decision 17',
`docs/intrinsic.md`) is such a fix: `memoryLocalDeclInitDrop`'s hidden
binder had no typed value naming the object the initializer was about to
allocate, until the binder's type admitted an unset local.
A refutation worth keeping goes in `Counterexamples/`, one file each.
