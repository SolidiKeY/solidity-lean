import Solidity.Calculus.RewriteSoundness
import Solidity.Wp.Verdict
import Solidity.Calculus.Completeness
import Solidity.Wp.Step
import Solidity.Wp.Terminal.Soundness
import Solidity.Examples.Common

/-!
# Configuration-level step soundness

`Calculus/RewriteSoundness.lean` lifts per-rule interpreter agreement through block
suffixes and rewrite derivations, but its top theorem
(`BlockReflMultiStep.execAgree`) *assumes* a global per-step soundness
premise, and the block-level relation cannot express terminal rules: an
empty residual block would identify a genuine state update with a no-op.

This module closes both gaps:

1. `ConfigStep` is a *configuration*-level step relation, on pairs of an
   open judgment and the interpreter state it is evaluated in. An `unfold`
   step carries its own soundness certificate (interpreter agreement modulo
   the calculus' scratch aliases, plus freshness of the untouched suffix and
   postcondition); an `exec` step consumes a *named* terminal rule's
   statement and advances the state by that rule's own update
   (`terminalUpdate`, `Wp/Terminal/Table.lean`) — exactly what the
   block-level relation cannot say. That the update is what the interpreter
   computes is `terminal_step_sound` (`Wp/Terminal/Soundness.lean`), used
   inside `holds_iff`.
   `ConfigStep.holds_iff` proves every step preserves judgment validity, and
   `ConfigMultiStep.holds_iff` chains it.

2. `SoundBlockStep`/`SoundBlockReflMultiStep` are evidence-carrying variants
   of `BlockStep`/`BlockReflMultiStep`; `SoundBlockReflMultiStep.execAgree`
   discharges the premise `BlockReflMultiStep.execAgree` had to assume —
   each step brings its own certificate (supplied in practice by the
   `_sound` theorems of `Calculus/RuleSoundness.lean`).
-/

namespace Solidity
namespace Wp

open Semantics RuleSoundness

/- The worked example at the end of this file evaluates the interpreter
by `simp`, which unfolds `SoliditySyntax.rootExpr`/`rootPlace`. Those are
matches on the variable *name*, and porting the solkey suites widened
them with the state variables of seven more contracts: the arm that fires
is unchanged, but the matcher application simp has to reduce is larger,
which is enough to exceed the default budget. -/
set_option maxHeartbeats 1000000

/-- A rewrite configuration: the open judgment together with the
interpreter state it is evaluated in. -/
abbrev Config := SolidityJudgment × Semantics.State

/-- The verdict is insensitive to executions that agree modulo the scratch
aliases, provided the postcondition is fresh for them. -/
theorem checkResult_congr {sm : SolidityModality} {post : WrappedExpr}
    {r₁ r₂ : Res State}
    (hr : ResultsAgree aliasNames r₁ r₂)
    (hpost : ∀ n ∈ aliasNames, usesVar post n = false) :
    checkResult sm post r₁ = checkResult sm post r₂ := by
  rcases ResultsAgree.cases hr with ⟨e, he₁, he₂⟩ | ⟨t₁, t₂, ht₁, ht₂, ht⟩
  · rw [he₁, he₂]
  · subst ht₁; subst ht₂
    have hv := evalValue_agree ht post hpost
    rcases ResAgree.cases hv with ⟨e, hv₁, hv₂⟩ | ⟨u₁, u₂, a, hv₁, hv₂, _⟩
    · simp [checkResult, hv₁, hv₂]
    · cases a with
      | bool b => simp [checkResult, hv₁, hv₂]
      | int v => simp [checkResult, hv₁, hv₂]

/-! ## The configuration step relation -/

/-- One step of symbolic execution at the configuration level. -/
inductive ConfigStep : Config -> Config -> Prop where
  /-- An unfold step: the head statement is rewritten to a (non-empty)
  residual, the state is unchanged, and the step carries its own soundness
  certificate (interpreter agreement at the carried state, modulo the scratch
  aliases) plus freshness of the untouched suffix and postcondition. -/
  | unfold {sm : SolidityModality} {lhs : Stmt} {cond : Prop}
      {rhs rest : Block} {post : WrappedExpr} {s : Semantics.State}
      (hrule : RuleStep sm lhs cond rhs)
      (hagree : RuleSoundness.ResultsAgree RuleSoundness.aliasNames
        (Semantics.execStmt s lhs) (Semantics.execBlock s rhs))
      (hfreshRest : ∀ n ∈ RuleSoundness.aliasNames,
        RuleSoundness.blockUsesVar rest n = false)
      (hfreshPost : ∀ n ∈ RuleSoundness.aliasNames,
        RuleSoundness.usesVar post n = false) :
      ConfigStep (⟨⟨sm, lhs :: rest⟩, post⟩, s) (⟨⟨sm, rhs ++ rest⟩, post⟩, s)
  /-- A terminal (exec) step of the *named* terminal rule `r`: the head
  statement is consumed and the state advances by `r`'s own update
  (`terminalUpdate`, `Wp/Terminal/Table.lean`).  The interpreter is
  not mentioned: that the update is what `execStmt` computes is the
  bridge theorem `terminal_step_sound`, applied in `holds_iff`.  This is
  the state-carrying step relation the port set out to build. -/
  | exec {sm : SolidityModality} {lhs : Stmt} {r : RuleName} {cond : Prop}
      {rest : Block} {post : WrappedExpr} {s s' : Semantics.State}
      (hrule : TerminalRuleStep sm lhs r cond)
      (hterm : hasUpdate r = true)
      (hupd : terminalUpdate r lhs s = .ok s') :
      ConfigStep (⟨⟨sm, lhs :: rest⟩, post⟩, s) (⟨⟨sm, rest⟩, post⟩, s')

/-- Every configuration step preserves judgment validity, in both
directions. -/
theorem ConfigStep.holds_iff {c₁ c₂ : Config} (h : ConfigStep c₁ c₂) :
    c₁.1.Holds c₁.2 ↔ c₂.1.Holds c₂.2 := by
  cases h with
  | @unfold sm lhs cond rhs rest post s hrule hagree hfreshRest hfreshPost =>
      have hblocks : ResultsAgree aliasNames
          (execBlock s (lhs :: rest)) (execBlock s (rhs ++ rest)) := by
        rw [execBlock, Semantics.execBlock_append]
        exact ResultsAgree.bind hagree
          fun t₁ t₂ ht => execBlock_agree ht rest hfreshRest
      simp only [SolidityJudgment.Holds, check_eq_checkResult,
        checkResult_congr hblocks hfreshPost]
  | @exec sm lhs r cond rest post s s' hrule hterm hupd =>
      have hexec : execStmt s lhs = .ok s' :=
        (terminal_step_sound s hterm hrule).trans hupd
      have hstep : execBlock s (lhs :: rest) = execBlock s' rest := by
        rw [execBlock, hexec]
        rfl
      simp only [SolidityJudgment.Holds, check_eq_checkResult, hstep]

/-! ## Multi-step closure -/

/-- Zero or more configuration steps. -/
inductive ConfigMultiStep : Config -> Config -> Prop where
  | refl {c : Config} : ConfigMultiStep c c
  | step {a b c : Config} :
      ConfigStep a b -> ConfigMultiStep b c -> ConfigMultiStep a c

/-- Validity transports across any configuration derivation. -/
theorem ConfigMultiStep.holds_iff {c₁ c₂ : Config} (h : ConfigMultiStep c₁ c₂) :
    c₁.1.Holds c₁.2 ↔ c₂.1.Holds c₂.2 := by
  induction h with
  | refl => exact Iff.rfl
  | step hstep _ ih => exact (ConfigStep.holds_iff hstep).trans ih

/-! ## Halting configurations

The verifier's terminal verdicts: a revert at the head validates a box
judgment outright, and any halt at the head refutes a diamond judgment
(and a stuck head refutes a box judgment). These are lemmas about the
judgment, not `ConfigStep` constructors — a halted execution has no
successor configuration. -/

/-- A reverting head statement validates a box judgment vacuously. -/
theorem holds_box_of_revert {lhs : Stmt} {rest : Block} {post : WrappedExpr}
    {s : State}
    (hexec : Semantics.execStmt s lhs = .error Semantics.Halt.revert) :
    (SolidityJudgment.mk ⟨SolidityModality.box, lhs :: rest⟩ post).Holds s := by
  have hblock : execBlock s (lhs :: rest) = .error Halt.revert := by
    rw [execBlock, hexec]
    rfl
  simp [SolidityJudgment.Holds, check_eq_checkResult, hblock, checkResult]

/-- A halting head statement refutes a diamond judgment. -/
theorem not_holds_diamond_of_halt {lhs : Stmt} {rest : Block}
    {post : WrappedExpr} {s : State} {h : Halt}
    (hexec : Semantics.execStmt s lhs = .error h) :
    ¬ (SolidityJudgment.mk ⟨SolidityModality.diamond, lhs :: rest⟩ post).Holds
        s := by
  have hblock : execBlock s (lhs :: rest) = .error h := by
    rw [execBlock, hexec]
    rfl
  cases h <;>
    simp [SolidityJudgment.Holds, check_eq_checkResult, hblock, checkResult]

/-- A stuck head statement refutes a box judgment. -/
theorem not_holds_box_of_stuck {lhs : Stmt} {rest : Block}
    {post : WrappedExpr} {s : State}
    (hexec : Semantics.execStmt s lhs = .error Semantics.Halt.stuck) :
    ¬ (SolidityJudgment.mk ⟨SolidityModality.box, lhs :: rest⟩ post).Holds
        s := by
  have hblock : execBlock s (lhs :: rest) = .error Halt.stuck := by
    rw [execBlock, hexec]
    rfl
  simp [SolidityJudgment.Holds, check_eq_checkResult, hblock, checkResult]

/-! ## Discharging `RewriteSoundness`'s assumed premise -/

/-- An evidence-carrying block step: `BlockStep.head` bundled with the
soundness certificate and suffix freshness that
`BlockStep.head_execAgree` consumes. -/
inductive SoundBlockStep : SolidityBlock -> SolidityBlock -> Prop where
  | head {sm : SolidityModality} {lhs : Stmt} {cond : Prop}
      {rhs rest : Block}
      (hrule : RuleStep sm lhs cond rhs)
      (hsound : ∀ s, RuleSoundness.ResultsAgree RuleSoundness.aliasNames
        (Semantics.execStmt s lhs) (Semantics.execBlock s rhs))
      (hfresh : ∀ n ∈ RuleSoundness.aliasNames,
        RuleSoundness.blockUsesVar rest n = false) :
      SoundBlockStep ⟨sm, lhs :: rest⟩ ⟨sm, rhs ++ rest⟩

/-- Zero or more evidence-carrying block steps. -/
inductive SoundBlockReflMultiStep : SolidityBlock -> SolidityBlock -> Prop where
  | refl {b : SolidityBlock} : SoundBlockReflMultiStep b b
  | step {a b c : SolidityBlock} :
      SoundBlockStep a b -> SoundBlockReflMultiStep b c ->
      SoundBlockReflMultiStep a c

/-- A single evidence-carrying step yields interpreter agreement. -/
theorem SoundBlockStep.execAgree {a b : SolidityBlock}
    (h : SoundBlockStep a b) :
    BlockExecAgree RuleSoundness.aliasNames a b := by
  cases h with
  | head hrule hsound hfresh =>
      exact BlockStep.head_execAgree hrule hsound hfresh

/-- Every evidence-carrying derivation yields interpreter agreement.  This
does not discharge `BlockReflMultiStep.execAgree`'s premise for free: a
`SoundBlockStep` must be *built* with a state-universal certificate
`∀ s, ResultsAgree …`, and only the unconditional `_sound` theorems of
`Calculus/RuleSoundness.lean` (its "Unconditional" shape — `ifElseTrue_sound`, the
declaration splits, the left-operand captures, `exprStmtCapture_sound`,
…) supply one.  The state-dependent theorems (those with `hlhs`, `hev`,
`hstable`, … hypotheses) cannot; a derivation using such a rule goes
through `ConfigStep`, which carries the state. -/
theorem SoundBlockReflMultiStep.execAgree
    {before after : SolidityBlock}
    (hsteps : SoundBlockReflMultiStep before after) :
    BlockExecAgree RuleSoundness.aliasNames before after := by
  induction hsteps with
  | refl => exact BlockExecAgree.refl _ _
  | step hstep _ ih => exact BlockExecAgree.trans hstep.execAgree ih

/-- Wiring check: a state-universal certificate — here `ifElseTrue_sound` —
is exactly what `SoundBlockStep.head` consumes. -/
example (thn els rest : Block)
    (hfresh : ∀ n ∈ RuleSoundness.aliasNames,
      RuleSoundness.blockUsesVar rest n = false) :
    SoundBlockStep
      ⟨.box, Stmt.ite (WrappedExpr.bool true) thn els :: rest⟩
      ⟨.box, (Rules.ruleEffect .ifElseTrue).block
        (Stmt.ite (WrappedExpr.bool true) thn els) trivial ++ rest⟩ :=
  SoundBlockStep.head
    (RuleStep.ofStepCase
      (UniquenessAux.firstStepCase_box (r := .ifElseTrue) (by decide) rfl
        trivial))
    (fun s => RuleSoundness.ifElseTrue_sound s _ thn els trivial)
    hfresh

/-! ### The LHS-unfold family is wireable now, and was not before

`SoundBlockStep.head` demands a *state-universal* certificate
`∀ s, ResultsAgree …`.  Before `Rules.freezeRhs`, the `*WriteUnfoldLeft*`
theorems carried `hev : rhsToSVal s rhs = .ok (s, sv)` and `hstable`, both of
which mention the state, so no `∀ s` could be formed from them and the whole
family was shut out of this machinery.  With the freeze their hypotheses are
`hcond`, `hprim` and `hfresh` — all state-independent — so `fun s => …` goes
through.  The example below is the check. -/

/-- `alice.account.balance = amount` is a `storageFieldWriteUnfoldLeftFst`
redex. -/
theorem exUnfoldCond :
    (Rules.ruleEffect .storageFieldWriteUnfoldLeftFst).cond
      sstmt!{ alice.account.balance = amount } := by
  change _ = true ∧ _ = true ∧ ¬ (_ = true)
  decide

/-- Wiring check for the unfold family: `storageFieldWriteUnfoldLeftFst_sound`
is state-universal, so it is exactly what `SoundBlockStep.head` consumes. -/
example (rest : Block)
    (hfresh : ∀ n ∈ RuleSoundness.aliasNames,
      RuleSoundness.blockUsesVar rest n = false) :
    SoundBlockStep
      ⟨.box, sstmt!{ alice.account.balance = amount } :: rest⟩
      ⟨.box, (Rules.ruleEffect .storageFieldWriteUnfoldLeftFst).block
        sstmt!{ alice.account.balance = amount } exUnfoldCond ++ rest⟩ :=
  SoundBlockStep.head
    (RuleStep.ofStepCase
      (UniquenessAux.firstStepCase_box
        (r := .storageFieldWriteUnfoldLeftFst) (by decide) rfl exUnfoldCond))
    (fun s =>
      RuleSoundness.storageFieldWriteUnfoldLeftFst_sound s _ _ _ _
        exUnfoldCond (by decide) (by decide))
    hfresh

/-! ## Wiring sanity example

A two-step `ConfigMultiStep` derivation on a tiny concrete judgment —
both steps are terminal `exec` steps of the `localValueAssign` rule —
and the transport of `Holds` across it. `native_decide` appears in this
example only. -/

namespace StepSoundnessExample

open SoliditySyntax Rules

/-- Compute a concrete interpreter equation: simp with the interpreter
equations normalizes both sides. -/
local macro "exec_eval" : tactic =>
  `(tactic| (simp [Semantics.execStmt, Semantics.execAssign,
                   Semantics.evalValue, Semantics.evalInt,
                   Semantics.resolveLoc, bind, Except.bind,
                   Semantics.State.getEnv, Semantics.State.setEnv,
                   Semantics.lookupBy, Semantics.setBy,
                   SoliditySyntax.intLitExpr, SoliditySyntax.varExpr,
                   SoliditySyntax.rootPlace, SoliditySyntax.varPlace,
                   SoliditySyntax.rootExpr,
                   -- Unfolding `rootExpr`/`rootPlace` exposes these, and
                   -- without them simp stops on the residue and leaves it
                   -- for `rfl` to whnf. That was survivable while the
                   -- name tables were small; with the solkey contracts'
                   -- state variables in them it exhausts the budget.
                   SoliditySyntax.originFor, SoliditySyntax.storageOriginFor,
                   SoliditySyntax.fieldFor,
                   StandardExample.stackUint, StandardExample.stackUintPlace,
                   Semantics.State.exampleStore];
             try rfl))

/-- The example judgment: `< result = 1; result = 2 > (result == 2)`. -/
def exJudgment : SolidityJudgment :=
  sol!{ < result = 1; result = 2 > (result == 2) }

/-- The state after the first assignment. -/
def exMid : State :=
  State.exampleStore.setEnv "result" (Binding.val (Value.int 1))

/-- The state after both assignments. -/
def exFinal : State :=
  exMid.setEnv "result" (Binding.val (Value.int 2))

/-- `localValueAssign` is the first (terminal) rule for `result = 1` under
diamond. -/
theorem exRule1 : TerminalRuleStep SolidityModality.diamond sstmt!{ result = 1 }
    RuleName.localValueAssign
    ((Rules.stepCase RuleName.localValueAssign).effect.cond
      sstmt!{ result = 1 }) :=
  UniquenessAux.firstStepCase_diamond (r := RuleName.localValueAssign)
    (by decide) (by decide) (by decide)

/-- … and for `result = 2`. -/
theorem exRule2 : TerminalRuleStep SolidityModality.diamond sstmt!{ result = 2 }
    RuleName.localValueAssign
    ((Rules.stepCase RuleName.localValueAssign).effect.cond
      sstmt!{ result = 2 }) :=
  UniquenessAux.firstStepCase_diamond (r := RuleName.localValueAssign)
    (by decide) (by decide) (by decide)

/-- The rule's update on the concrete statement, computed: `localValueAssign`'s
update is `assignStackRead`, a stack read followed by a stack bind. -/
theorem terminalUpdate_localValueAssign (stmt : Stmt) (s : State) :
    terminalUpdate RuleName.localValueAssign stmt s =
      onAssign assignStackRead stmt s := rfl

local macro "upd_eval" : tactic =>
  `(tactic| (rw [terminalUpdate_localValueAssign];
             simp [onAssign, assignStackRead,
                   assignStack, readVal, stackVal, bind, Except.bind, Except.map,
                   Semantics.State.setEnv, Semantics.lookupBy, Semantics.setBy,
                   SoliditySyntax.intLitExpr, SoliditySyntax.varExpr,
                   SoliditySyntax.rootPlace, SoliditySyntax.varPlace,
                   SoliditySyntax.rootExpr,
                   SoliditySyntax.originFor, SoliditySyntax.storageOriginFor,
                   SoliditySyntax.fieldFor,
                   StandardExample.stackUint, StandardExample.stackUintPlace,
                   Semantics.State.exampleStore];
             try rfl))

set_option maxHeartbeats 4000000 in
/-- The two-step configuration derivation: both statements execute as
terminal steps, threading the state through. -/
theorem exSteps : ConfigMultiStep
    (exJudgment, State.exampleStore)
    (⟨⟨SolidityModality.diamond, []⟩, exJudgment.post⟩, exFinal) := by
  refine ConfigMultiStep.step
    (b := (⟨⟨SolidityModality.diamond, [sstmt!{ result = 2 }]⟩,
      exJudgment.post⟩, exMid)) ?_
    (ConfigMultiStep.step ?_ ConfigMultiStep.refl)
  -- `exMid`/`exFinal` are unfolded here rather than left to `rfl`: the
  -- goal is `execStmt … = .ok exMid`, and whnf-ing the right-hand side
  -- through `exampleStore` is what blows the budget.
  · exact ConfigStep.exec exRule1 rfl (by simp only [exMid]; upd_eval)
  · exact ConfigStep.exec exRule2 rfl (by simp only [exFinal, exMid]; upd_eval)

/-- Transport `Holds` backwards across the derivation: validity of the
fully executed configuration gives validity of the original judgment. -/
example : exJudgment.Holds State.exampleStore :=
  (ConfigMultiStep.holds_iff exSteps).mpr (by native_decide)

end StepSoundnessExample

end Wp
end Solidity
