import Solidity.Yul.LocalDefaultHorizon
import Solidity.Yul.Checks.LocalDefaultRepresentation

/-! Typed numeric-default prefix and block-restoration horizon controls.
Surviving dirty Boolean constructors are preserved, not cleaned. -/
namespace Solidity.Yul.Checks.LocalDefaultHorizon

theorem completedObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.full (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world
  rfl

theorem completedStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env) (extra : Nat), Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) (5+extra) (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.full (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world extra
  exact Solidity.Yul.LocalDefaultHorizon.extension _ _ _ _ _ _ _ _ 5 extra _ _ (completedObserved world)

theorem blockObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultItems.blockRun (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world
  rfl

theorem blockStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env) (extra : Nat), Solidity.Yul.LocalDefaultItems.blockRun (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) (6+extra) (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world extra
  exact Solidity.Yul.LocalDefaultHorizon.blockExtension _ _ _ _ _ _ _ _ 6 extra _ _ (blockObserved world)

theorem beforeGrowth : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 2 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world
  rfl

theorem firstGrowth : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 3 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultRepresentation.first (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world
  rfl

theorem fullGrowth : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 4 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultRepresentation.full (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world
  rfl

theorem timeoutMayChange : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 4 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) ≠ Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world same
  rw [fullGrowth,completedObserved] at same
  cases same

theorem dirtyProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalDefaultItems.blockRun (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) (6+extra) (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world)) = none := by
  intro world extra
  rw [blockStable]
  rfl

theorem unsupportedStatement : ¬ Nonempty (Solidity.Yul.LocalDefaultItems.Supported Solidity.Yul.Checks.LocalDefaultRepresentation.env [] false ⟨false,false⟩ (.stmt (.expr (.compare .eq (.bool true) (.bool false))) (Solidity.Source.RItems.nil (Γ := [.bool])))) := by
  intro witness
  rcases witness with ⟨proof⟩
  cases proof with
  | body child =>
    cases child with
    | expression child tail =>
      cases child with
      | base child => cases child

#print axioms Solidity.Yul.LocalDefaultHorizon.successor
#print axioms Solidity.Yul.LocalDefaultHorizon.extension
#print axioms Solidity.Yul.LocalDefaultHorizon.blockSuccessor
#print axioms Solidity.Yul.LocalDefaultHorizon.blockExtension
#print axioms completedObserved
#print axioms completedStable
#print axioms blockObserved
#print axioms blockStable
#print axioms beforeGrowth
#print axioms firstGrowth
#print axioms fullGrowth
#print axioms timeoutMayChange
#print axioms dirtyProjection
#print axioms unsupportedStatement

end Solidity.Yul.Checks.LocalDefaultHorizon
