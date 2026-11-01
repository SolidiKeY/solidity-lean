import Solidity.Calculus.CallFunctionSearch
import Solidity.Examples.Tactics.CallFunctionPlan

/-! # Checked-plan acceptance, refusal and semantic controls
Concrete producer results, not only generic laws for hypothetical plans.
-/
namespace Solidity.Examples.Tactics.CallFunctionSearch
open Solidity.CallFunctionPlan Solidity.CallFunctionTable Solidity.CallFunctionSearch
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .uint, .val .uint]
private def name : Var := .fresh "same" 0
private def affine {Δ : Ctx} (x : Val C Δ .uint) : Val C Δ .uint :=
  .binop .add rfl rfl (.binop .mul rfl rfl x (.simple (.lit 3 rfl))) (.simple (.lit 1 rfl))
private def base : Tm C (.val .uint :: Γ) (.val .uint) :=
  (affine (.simple (.local .here))).lower
private def nested (n : Nat) (v : Val C Γ .uint) : Val C Γ .uint :=
  match n with
  | 0 => v
  | n+1 => affine (nested n v)
private def oldTerm (k : Nat) : Tm C Γ (.val .uint) :=
  (nested (2^k) (.simple (.local (.there .here)))).lower
private def original (n : Nat) : State C Γ :=
  (({ State.init C with selfBalance := uintOfNat 5 }).push
    (t := .val .uint) (uintOfNat n)).push (t := .val .uint) (uintOfNat 99)
private def post (n : Nat) : Fml C Γ := .eq (.pvV .here) (.app0 (.lit (uintOfNat n)))

/-- Automatic search chooses an actual checked plan, without supplied
base, input position or doubling level, at several distinct levels. -/
theorem finds :
    (search? (oldTerm 1)).isSome = true ∧
    (search? (oldTerm 2)).isSome = true ∧
    (search? (oldTerm 3)).isSome = true ∧
    (search? (oldTerm 4)).isSome = true := by decide +kernel

/-- Selected metadata comes from the exact returned plan, not a guessed row. -/
theorem selectedMetadata : (search? (oldTerm 3)).map
    (fun plan => (plan.level, plan.base.size, plan.input.toNat)) = some (3,5,1) := by
  decide +kernel

/-- The fixed proposal width is exercised while retaining the real inner base. -/
theorem proposalWidths : (subterms (oldTerm 0)).length = 5 ∧
    (subterms (oldTerm 1)).length = 9 ∧ (subterms (oldTerm 2)).length = 17 ∧
    (subterms (oldTerm 3)).length = 32 := ⟨rfl, rfl, rfl, rfl⟩

/-- An actual automatic selection has a meaningful inhabited emitted leaf. -/
theorem selectedReturns (m : Modality) : ∃ plan : Plan (oldTerm 1),
    search? (oldTerm 1) = some plan ∧
    holds (original 2) (plan.leaf m name name name .here (post 22)) := by
  obtain ⟨plan, hp⟩ := Option.isSome_iff_exists.mp finds.1
  refine ⟨plan, hp, ?_⟩
  exact Solidity.Examples.Tactics.CallFunctionPlan.returning plan m

/-- A literal has no proposed input and stays on its ordinary route. -/
theorem literalRefusal :
    (search? (Tm.app0 (C := C) (Γ := Γ) (.lit (uintOfNat 7)))).isSome = false := rfl

private def broken : Tm C Γ (.val .uint) :=
  (Val.binop .add rfl rfl
    (.binop .mul rfl rfl (affine (.simple (.local (.there .here)))) (.simple (.lit 3 rfl)))
    (.simple (.lit 2 rfl))).lower

/-- A changed final offset is not a repeated instance of its inner body. -/
theorem nearMatchRefusal : (search? broken).isSome = false := by decide +kernel

private def conditional : Tm C Γ (.val .uint) :=
  .app3 .ite (.app0 (.lit true)) (oldTerm 1) (oldTerm 2)

/-- The existing literal/value input collector refuses conditionals for this
optional search; no source verdict or ordinary path is changed. -/
theorem conditionalRefusal : (search? conditional).isSome = false := rfl

private def withCoefficient (x : Val C Γ .uint) : Val C Γ .uint :=
  .binop .add rfl rfl (.binop .mul rfl rfl x (.simple (.local .here))) (.simple (.lit 1 rfl))
private def coefficientTerm : Tm C Γ (.val .uint) :=
  (withCoefficient (withCoefficient (.simple (.local (.there .here))))).lower

/-- Multiple old locals distinguish the true input from a captured coefficient. -/
theorem coefficientInput : (search? coefficientTerm).map
    (fun plan => (plan.level, plan.base.size, plan.input.toNat)) = some (1,5,1) := by
  decide +kernel

/-- The automatically chosen plan can write the captured coefficient only
at the end, while all intermediate calls still read its original99. -/
theorem coefficientReturns (m : Modality) : ∃ plan : Plan coefficientTerm,
    search? coefficientTerm = some plan ∧
    holds (original 2) (plan.leaf m name name name .here (post 19702)) := by
  have found : (search? coefficientTerm).isSome = true := by decide +kernel
  obtain ⟨plan, hp⟩ := Option.isSome_iff_exists.mp found
  refine ⟨plan, hp, ?_⟩
  apply (plan.holds m name name name .here (post 19702) (original 2)).mpr
  apply CallResultCapture.sound name .here coefficientTerm (post 19702) (original 2)
  apply (CallResultRestore.holds_leaf_of_eval m name .refl .here coefficientTerm (post 19702)
    (original 2) (uintOfNat 19702) rfl).mpr
  rfl

private def addOnes (n : Nat) (x : Val C Γ .uint) : Val C Γ .uint :=
  match n with
  | 0 => x
  | n+1 => .binop .add rfl rfl (addOnes n x) (.simple (.lit 1 rfl))
private def beyondProposals : Tm C Γ (.val .uint) :=
  (addOnes 34 (.simple (.local (.there .here)))).lower

/-- A capped retained-prefix/refusal control preserves the actual cap. -/
theorem cappedRefusal : (subterms beyondProposals).length = 32 ∧
    (search? beyondProposals).isSome = false := by decide +kernel

private def wideBase : Tm C (.val .uint :: Γ) (.val .uint) :=
  Nat.rec (.pvV .here)
    (fun _ t => .app2 (.binop .add rfl) t (.app0 (.lit (uintOfNat 1)))) 17

/-- An actual successful explicit candidate exists outside the retained size
prefix. Automatic search is deliberately incomplete; refusal is conservative. -/
theorem explicitBeyondPrefix :
    wideBase.size = 35 ∧
    (subterms beyondProposals).all (fun t => t.size < wideBase.size) = true ∧
    (checked? wideBase 1 (.there .here) beyondProposals).isSome = true := by
  decide +kernel

end Solidity.Examples.Tactics.CallFunctionSearch
