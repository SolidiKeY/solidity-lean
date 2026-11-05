import Solidity.Calculus.DecisionNumericGround
import Solidity.Examples.DecisionCoefficientBoundary

/-! # Inhabited closed numeric leaf controls -/
namespace Solidity.Examples.DecisionNumericGround
open Solidity.Decide
open Solidity.Examples.DecisionCoefficientBoundary (Bank)
set_option Elab.async false

def closedTrue : Fml Bank [] := .tt
def closedFalse : Fml Bank [] := .not .tt

theorem actual_closed_leaves : leafOf? closedTrue = some .tt ∧
    leafOf? closedFalse = some (.not .tt) := by constructor <;> rfl

theorem closed_covered : closedTrue.Covered = true ∧ closedFalse.Covered = true := by
  constructor
  · exact qfUIntGround_Covered_of_leaf .tt (by decide +kernel) actual_closed_leaves.1
  · exact qfUIntGround_Covered_of_leaf (.not .tt) (by decide +kernel) actual_closed_leaves.2

def optionalBoth : LFml Bank := LFml.optEq (.err (s := .val .uint)) .err
def optionalMismatch : LFml Bank := LFml.optEq (.err (s := .val .uint)) (.app0 (.lit ⟨0, by decide⟩))

theorem optional_grammars :
    optionalBoth.UIntQF (fun _ => False) (fun _ => False) ∧
    optionalMismatch.UIntQF (fun _ => False) (fun _ => False) := by
  exact ⟨.optEq .err .err, .optEq .err (.lit _)⟩

theorem optional_exact_controls :
    optionalBoth.inExact = true ∧ optionalBoth.exactBounded = true ∧
    optionalMismatch.inExact = true ∧ optionalMismatch.exactBounded = true := by
  obtain ⟨ha, hb⟩ := optional_grammars.1.ground_exact_tests (by decide +kernel)
  obtain ⟨hc, hd⟩ := optional_grammars.2.ground_exact_tests (by decide +kernel)
  exact ⟨ha, hb, hc, hd⟩

theorem optional_semantic_controls :
    optionalBoth.holds (State.init Bank) AEnv.dflt ∧
    ¬ optionalMismatch.holds (State.init Bank) AEnv.dflt := by
  constructor
  · exact (LFml.optEq_holds _ _ _ _).mpr rfl
  · intro h
    have he : (none : Option PrimTy.uint.Denote) = some ⟨0, by decide⟩ :=
      (LFml.optEq_holds _ _ _ _).mp h
    cases he

/-- Bound-variable grammar is outside the closed class, regardless of node budget. -/
theorem free_parameter_not_ground :
    ¬ (LFml.eq (p := .uint) (.var 0) (.var 0) : LFml Bank).UIntQF (fun _ => False) (fun _ => False) := by
  intro h
  exact h.parameters ⟨.uint, 0⟩ (by decide +kernel)

end Solidity.Examples.DecisionNumericGround
