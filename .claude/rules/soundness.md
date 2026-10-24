---
paths:
  - "Solidity/Calculus/Sound*.lean"
  - "Solidity/Calculus/Sound/*.lean"
  - "Solidity/Calculus/ProvesSound.lean"
  - "Solidity/Calculus/Logic.lean"
  - "Solidity/Calculus/Symex.lean"
  - "Solidity/Counterexamples/*.lean"
---

# Soundness conventions

**The contract**: `Stmt.sound` (`Calculus/Sound.lean`) proves every rule
`Stmt.step` fires correct for its statement (`Stmt.Sound C`, from
`Premise.Sound`, `Calculus/ProvesSound.lean`), against the typed run
(`Stmt.run`, `Semantics/Run.lean`), in every typed state, at any fresh index,
with no hypothesis. A taclet is sound because its premise is the one
`Stmt.step` builds (`Taclet.toStep`, `Calculus/Taclet.lean`): there is no
proof per taclet. `Proves.sound`/`Proves.fmlValid` and `symex_sound` lift it to
derivations; a leaf the closer proves is sound on its scoped form
(`Fml.Valid.of_reduceS`, `Calculus/DecideTyped.lean`). `#print axioms` on
them shows only `propext`, `Classical.choice`, `Quot.sound`. Keep it that
way: no `sorry`, no new hypothesis.

## Proving a new arm

Use **`docs/rule-repair.md`** before broad integration.
State and attempt the local agreement/simulation lemma in the scratch
prototype; do not defer all semantic checking until the rule is registered.
Concrete agreement and bounded example closure are rejection gates, not
substitutes for the general proof below.

- **The shape** (`Calculus/SoundKit.lean`): state what the premise asks of
  the statement's typed run (`Premise.Runs`); the premise kinds' lemmas
  (`Premise.sound_update` … `sound_done`) turn it into `Premise.Sound`. Name
  the arm's theorem `…_sound` and add it to `Stmt.stepSound_arms`
  (`Calculus/SoundStep.lean`), or to the blocks' (`SoundCalls`,
  `SoundLoops`).
- **Update premise** (`Calculus/SoundArms.lean`): an update is a term of
  `Update.lean`, computed on the typed state as a global part and the
  locals' values (`Upd.applyV`), so state an equation between what it
  computes and the statement's typed step (`*_agrees`, `TRes.Agrees` of
  `TRun.x` against `U.applyV σ`, the step's state read as the typed global
  part and the locals' values, the operands through
  `Calculus/LowerRun.lean`), and close with `Premise.sound_update_typed`.
- **Two sequential updates** (`Premise.updates U V`): establish
  `Premise.UpdatesRuns`. `Upd.PairLands` supplies a typed intermediate state
  linking both successful updates; `Upd.PairFails` covers ordinary failure
  in either stage, with exhaustion excluded explicitly. Use
  `Premise.sound_updatesH` for ordinary soundness; the same conditions give
  `holdsC_updates` for a statement with no callback of its own. Keep the
  initial two-update shape; merge only by an explicit update rewrite.
- **Guarded sequential updates** (`Premise.guardedUpdates c U V`): keep
  division/remainder's nonzero test outside both updates. Prove
  `Premise.GuardedUpdatesRuns`: `c` reads no callback, its true branch has
  `UpdatesRuns`, and its false branch simulates `revert` through `TRes.Sim`.
  The latter permits the existing exhaustion boundary, never success or panic.
- **Unfold premise** (`Calculus/SoundCapture.lean`, `SoundLocal`, …): the
  fresh local is pushed and popped by the premise's frame; the runs compare
  up to the halt (`TRes.Sim`, `sound_unfoldSim`), the schema variables read
  under the fresh local by the shift lemmas (`Val.evalT_up` and kin).
- Under the diamond the typed run must not diverge where the update ends:
  an evaluator and every write but a push end (`Semantics/Ends.lean`); a
  push at the bound is `exhausted`, which both modalities accept.
- Develop an arm as a standalone lemma in a scratch module importing
  `Calculus/SoundKit.lean`; the arms' files elaborate in tens of seconds.

## A new rule: one file in `Calculus/Sound/`

The existing arms stay where they are (`SoundArms` … `SoundLoops`).  A rule
added from now on proves its arm in a file of its own,
`Calculus/Sound/<Arm>.lean` (`Calculus/Sound/README.md`), so that it
elaborates alone and in parallel with the others.  Soundness is per
`Stmt.step` arm, not per taclet: a taclet added to an existing statement
extends that statement's `…Step_sound` where it is.

```lean
import Solidity.Calculus.SoundKit   -- or the arms' file it builds on

/-!
# `<Arm>`'s rules are sound

What the premise asks of the statement's typed run, in a sentence.
-/

namespace Solidity
open Solidity (Modality)
variable {C : Contract} {m : Modality} {Γ Γ' : Ctx} (σ : State C Γ)

/-- **`<arm>Step`'s premise is what the statement's typed run does.** -/
theorem <arm>Step_sound (k : Nat) … (q : Premise C Γ Γ')
    (hs : <arm>Step k … = q) : Premise.Runs m (.<ctor> …) q σ := by
  …

-- paste what `#print axioms` prints: a subset of these three
/-- info: 'Solidity.<arm>Step_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms <arm>Step_sound

end Solidity
```

Then register it: `Calculus/SoundStep.lean` imports the file and its
`Stmt.stepSound_arms` case calls the theorem (`exact <arm>Step_sound σ k …
p hp`); a block's file is imported by `Calculus/StmtSound.lean`, beside
`SoundCalls`, `SoundLoops` and `SoundCatch`, and its `Stmt.stepSound` case
calls it; and `docs/lean-key-rule-map.md` gets the rule's row, naming
the file.  The `cases s` there is exhaustive, so a rule without its lemma
fails the build.  `docs/parallelism.md` ("Adding a rule: the six places")
lists the places a new rule is registered.

## When a case is false

Do not weaken the theorem. Find the state where the premise and the statement
end differently, check which one solc agrees with, and fix that side: the rule
(`Calculus/Rules.lean`, its arm) or the run (`Semantics/Run.lean`, recording
it in `docs/solc-alignment.md`). An unset memory local (decision 17',
`docs/intrinsic.md`) is such a fix: `memoryLocalDeclInitDrop`'s hidden
binder had no typed value naming the object the initializer was about to
allocate, until the binder's type admitted an unset local.
A refutation worth keeping goes in `Counterexamples/`, one file each.
