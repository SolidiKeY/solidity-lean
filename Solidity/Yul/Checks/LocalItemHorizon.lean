import Solidity.Yul.LocalItemHorizon
import Solidity.Yul.Checks.LocalBoolItemRepresentation

namespace Solidity.Yul.Checks.LocalItemHorizon
export LocalBoolItemRepresentation (env state raw cleanTrue cleanFalse)
def doubleBody : Solidity.Source.RItems env [] false ⟨false,false⟩ [.bool] [.bool,.bool,.bool] :=
  .stmt (.declInit (τ := .bool) (.local .here) (by rfl))
    (.stmt (.declInit (τ := .bool) (.unary .not (.local .here)) (by rfl)) .nil)
def doubleProof : LocalBoolItems.Supported env [] false ⟨false,false⟩ doubleBody :=
  .declaration (.base (.local .here))
    (.declaration (.not (.base (.local .here))) .nil)
def doubleWitness : Nonempty (LocalBoolItems.Supported env [] false ⟨false,false⟩ doubleBody) :=
  ⟨doubleProof⟩
def doubleFinal (world : Solidity.Source.St env) : LocalState env [.bool,.bool,.bool] :=
  ((cleanFalse,(raw 2,(raw 2,()))),world)


theorem completedStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof (6+extra) (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolItemRepresentation.finalState world) := by
  intro world extra
  exact Solidity.Yul.LocalItemHorizon.extension _ _ _ _ _ _ _ _ 6 extra _ _ (Solidity.Yul.Checks.LocalBoolItemRepresentation.completed world)

theorem doubleCompleted : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalItemHorizon.doubleProof 5 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalItemHorizon.doubleFinal world) := by
  intro world
  rfl

theorem doubleStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalItemHorizon.doubleProof (5+extra) (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalItemHorizon.doubleFinal world) := by
  intro world extra
  exact Solidity.Yul.LocalItemHorizon.extension _ _ _ _ _ _ _ _ 5 extra _ _ (doubleCompleted world)

theorem beforeGrowth : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalItemHorizon.doubleProof 2 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) := by
  intro world
  rfl

theorem afterGrowth : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalItemHorizon.doubleProof 4 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolItemRepresentation.extended world) := by
  intro world
  rfl

theorem partialRetained : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 5 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolItemRepresentation.extended world) := by
  intro world
  rfl

theorem timeoutMayChange : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 5 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) ≠ Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 6 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) := by
  intro world same
  rw [partialRetained,Solidity.Yul.Checks.LocalBoolItemRepresentation.completed] at same
  cases same

theorem dirtyProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalItemHorizon.doubleProof (5+extra) (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world)) = none := by
  intro world extra
  rw [doubleStable]
  rfl

theorem unsupportedStatement : ¬ Nonempty (Solidity.Yul.LocalBoolItems.Supported Solidity.Yul.Checks.LocalBoolItemRepresentation.env [] false ⟨false,false⟩ (.stmt (.expr (.compare .eq (.bool true) (.bool false))) (Solidity.Source.RItems.nil (Γ := [.bool])))) := by
  intro witness
  rcases witness with ⟨proof⟩
  cases proof with
  | expression child tail =>
    cases child with
    | base child => cases child

#print axioms Solidity.Yul.LocalItemHorizon.successor
#print axioms Solidity.Yul.LocalItemHorizon.extension
#print axioms completedStable
#print axioms doubleCompleted
#print axioms doubleStable
#print axioms beforeGrowth
#print axioms afterGrowth
#print axioms partialRetained
#print axioms timeoutMayChange
#print axioms dirtyProjection
#print axioms unsupportedStatement

end Solidity.Yul.Checks.LocalItemHorizon
