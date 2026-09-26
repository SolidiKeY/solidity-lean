import Solidity.Kernel.Bridge

/-!
# One rule per statement

`Taclet.rule_step`: whatever derivation a statement has, its last step is
the rule `Stmt.step` picks, by solkey taclet (`Taclet.origin_step`) and by
the old table's name (`Taclet.rule_step`).  So at most one rule runs a
statement, up to the scratch names it binds (`Taclet.origin_unique`).

KeY leaves some of these open and lets its strategy choose; the kernel's
side conditions choose instead, in `Stmt.step`'s order:

- a conditional in a write is lowered, never captured (`Val.notTernary`);
- a copy between two storage paths unfolds its target first, and its source
  only once the target is simple (`Loc.isTarget`);
- a memory reference unfolds its source first, and its target only once the
  source is bindable (`MPath.isBindable`).

The proof splits each constructor down to the atoms `Stmt.step` branches
on and evaluates the step: the tactics below are that split and nothing else.
-/

namespace Solidity
namespace Kernel

open Semantics

variable {C : Contract} {m : Modality}

theorem Step.rule_dite {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {c : Prop} [Decidable c]
    {t : c → Step C m s} {e : ¬c → Step C m s} :
    (dite c t e).2.rule = dite c (fun h => (t h).2.rule) (fun h => (e h).2.rule) := by
  by_cases h : c
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]

theorem Step.origin_dite {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {c : Prop} [Decidable c]
    {t : c → Step C m s} {e : ¬c → Step C m s} :
    (dite c t e).2.origin = dite c (fun h => (t h).2.origin) (fun h => (e h).2.origin) := by
  by_cases h : c
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]

open Lean Meta Elab Tactic in
/-- Split the value or path a hypothesis `v.isSimple = false` names. -/
local elab "cases_nonsimple" : tactic => withMainContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if let some (_, lhs, rhs) := ty.eq? then
      if (lhs.isAppOf ``Val.isSimple || lhs.isAppOf ``SPath.isSimple) && rhs.isConstOf ``Bool.false then
        let v := lhs.appArg!
        let v := if v.isAppOf ``SPath.loc then v.appArg! else v
        if v.isFVar then
          liftMetaTactic fun g => do
            let subs ← g.cases v.fvarId!
            return subs.toList.map (·.mvarId)
          return
  throwError "no non-simple value"

open Lean Meta Elab Tactic in
/-- Split the value a hypothesis `v.isSimple = true` names. -/
local elab "cases_simple" : tactic => withMainContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if let some (_, lhs, rhs) := ty.eq? then
      if lhs.isAppOf ``Val.isSimple && rhs.isConstOf ``Bool.true then
        let v := lhs.appArg!
        if v.isFVar then
          liftMetaTactic fun g => do
            let subs ← g.cases v.fvarId!
            return subs.toList.map (·.mvarId)
          return
  throwError "no simple value"

/-- A simple target's index is a simple value: split it. -/
local macro "target_simp" : tactic => `(tactic| (
  have hT := ‹Loc.isTarget _ = true›
  simp only [Loc.isTarget, Bool.and_eq_true] at hT
  try obtain ⟨_, _⟩ := hT
  (try cases_simple) <;> (try contradiction)))

/-- Evaluate the step, plainly. -/
local macro "step_simp0" : tactic => `(tactic| simp only [Stmt.step, localStep, assignStep, rebindStep, deleteStep, binopRightStep, shortCircuitStep,
      copyStep, opStep, incStep, assignIncStep, ternaryStep, pushStep, popStep, bindPushStep, transferStep, rebindMemStep,
      declMemStep, assignMemStep, assignFromMemStep, fieldLeftFstStep, indexLeftFstStep, indexCaptureStep,
      memValStep, MHole.unfoldStep, Hole.unfoldStep, Hole.fill,
      MHole.fill, VHole.fill, dite_true, dite_false, Bool.false_eq_true, and_self, and_true, true_and,
      eq_self_iff_true, ↓reduceDIte, Step.rule_dite, Step.origin_dite, *])

/-- Evaluate the step, through the side conditions. -/
local macro "step_simp" : tactic => `(tactic| simp only [Stmt.step, localStep, assignStep, rebindStep, deleteStep, binopRightStep, shortCircuitStep,
      copyStep, opStep, incStep, assignIncStep, ternaryStep, pushStep, popStep, bindPushStep, transferStep, rebindMemStep,
      declMemStep, assignMemStep, assignFromMemStep, fieldLeftFstStep, indexLeftFstStep, indexCaptureStep,
      memValStep, MHole.unfoldStep, Hole.unfoldStep, Hole.fill,
      MHole.fill, VHole.fill, dite_true, dite_false, Bool.false_eq_true, and_self, and_true, true_and,
      eq_self_iff_true, ↓reduceDIte, Step.rule_dite, Step.origin_dite, MPath.isBindable, SPath.isBindable, Bool.and_eq_true, Src.isSimple, Loc.isTarget, Val.notTernary, Val.isSimple, dite_eq_ite, ite_self, *])

/-- Evaluate the step through every branch left open. -/
local macro "step_fin" : tactic => `(tactic| repeat' (first | rfl | step_simp | split))

/-- Split a derivation to the atoms the step branches on, and evaluate it. -/
local macro "rule_step_tac" : tactic => `(tactic| (
  cases ‹Taclet _ _ _ _›
  case storageToMemoryDeclUnfoldRightFst hnf _ _ _ _ =>
    cases ‹Modality› <;> cases_nonsimple <;> (try contradiction) <;> cases_nonsimple <;> (try contradiction) <;>
      step_fin <;> exact absurd (hnf _ _ _ _ rfl) (by simp [*])
  all_goals first
    | (cases ‹Modality› <;> (try cases ‹Hole _ _ _ _›) <;> (try cases ‹MHole _ _ _ _›) <;> (try cases ‹VHole _ _ _›) <;>
        (try cases_nonsimple) <;> (try contradiction) <;> (try cases_nonsimple) <;> (try contradiction) <;>
        first | (step_simp0 <;> rfl) | (step_simp <;> rfl))
    | (cases ‹Modality› <;> (try cases ‹Hole _ _ _ _›) <;> (try cases ‹MHole _ _ _ _›) <;> (try cases ‹VHole _ _ _›) <;>
        (try cases ‹Kernel.Loc _ _ _›) <;> (try cases ‹MLoc _ _ _›) <;> (try target_simp) <;>
        (try cases_nonsimple) <;> (try contradiction) <;> (try cases_nonsimple) <;> (try contradiction) <;>
        step_fin <;> done)))

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- A derivation's last step is the solkey taclet `Stmt.step` picks: of
`folks[1].account = folks[2].account;` the only one is
`storageFieldWriteStorageRef_unfold_leftFst`, never
`storageFieldRead_unfold_rightFst`. -/
theorem Taclet.origin_step {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'}
    (d : Taclet C m s pr) : d.origin = (s.step m).2.origin := by
  rule_step_tac

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- A derivation's last step is the old table's rule `Stmt.step` picks:
`folks[1].account = folks[2].account;` is only
`storageFieldWriteStorageRefUnfoldLeftFst`. -/
theorem Taclet.rule_step {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'}
    (d : Taclet C m s pr) : d.rule = (s.step m).2.rule := by
  rule_step_tac

/-- Two derivations of one statement end in the same solkey taclet:
`folks[x].age = 1;` captures its index or unfolds its receiver, never both,
whatever the derivations name their scratch locals. -/
theorem Taclet.origin_unique {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr₁ pr₂ : Premise C Γ Γ'}
    (d₁ : Taclet C m s pr₁) (d₂ : Taclet C m s pr₂) : d₁.origin = d₂.origin := by
  rw [d₁.origin_step, d₂.origin_step]

/-- Two derivations of one statement end in the same rule of the old
table. -/
theorem Taclet.rule_unique {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr₁ pr₂ : Premise C Γ Γ'}
    (d₁ : Taclet C m s pr₁) (d₂ : Taclet C m s pr₂) : d₁.rule = d₂.rule := by
  rw [d₁.rule_step, d₂.rule_step]

section Examples

local instance instUniqueContract : InContract := ⟨StandardExample⟩

/-- `folks[1].account = folks[2].account;` unfolds its target first: KeY
could unfold either side. -/
example : match ksol{ folks[1].account = folks[2].account; } with
    | .cons s .nil => ∀ pr (d : Taclet StandardExample .box s pr),
        d.origin = .taclet .storageFieldWriteStorageRef_unfold_leftFst
    | _ => False :=
  fun _ d => d.origin_step.trans rfl

end Examples

end Kernel
end Solidity
