import Solidity.Yul.LocalBoolHorizon
import Solidity.Yul.Checks.LocalBoolControlRepresentation

namespace Solidity.Yul.Checks.LocalBoolHorizon
def selected : LocalBoolControl.Supported LocalBoolControlRepresentation.env [.bool]
    (.cond (.local .here) (.assign (.local .here) (.bool true))
      (.unary .not (.unary .not (.unary .not (.local .here))))) :=
  .cond LocalBoolControlRepresentation.read LocalBoolControlRepresentation.setTrue
    (.not (.not (.not LocalBoolControlRepresentation.read)))
def witness : Nonempty (LocalBoolControl.Supported LocalBoolControlRepresentation.env [.bool]
    (.cond (.local .here) (.assign (.local .here) (.bool true))
      (.unary .not (.unary .not (.unary .not (.local .here)))))) := ⟨selected⟩


theorem andStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.andProof (2+extra) (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.ok Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanFalse,(Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world)) := by
  intro world extra
  have terminal : (Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.andProof 2 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world)).1 ≠ .error .timeout := by
    rw [Solidity.Yul.Checks.LocalBoolControlRepresentation.andSkip]
    intro impossible
    cases impossible
  exact (Solidity.Yul.LocalBoolHorizon.extension _ _ _ _ 2 extra _ terminal).trans (Solidity.Yul.Checks.LocalBoolControlRepresentation.andSkip world)

theorem orStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.orProof (2+extra) (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.ok (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2),(Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world)) := by
  intro world extra
  have terminal : (Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.orProof 2 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world)).1 ≠ .error .timeout := by
    rw [Solidity.Yul.Checks.LocalBoolControlRepresentation.orRetains]
    intro impossible
    cases impossible
  exact (Solidity.Yul.LocalBoolHorizon.extension _ _ _ _ 2 extra _ terminal).trans (Solidity.Yul.Checks.LocalBoolControlRepresentation.orRetains world)

theorem conditionalStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.condProof (3+extra) (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.ok Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanFalse,Solidity.Yul.Checks.LocalBoolControlRepresentation.state Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanFalse world) := by
  intro world extra
  have terminal : (Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.condProof 3 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world)).1 ≠ .error .timeout := by
    rw [Solidity.Yul.Checks.LocalBoolControlRepresentation.conditionalUpdate]
    intro impossible
    cases impossible
  exact (Solidity.Yul.LocalBoolHorizon.extension _ _ _ _ 3 extra _ terminal).trans (Solidity.Yul.Checks.LocalBoolControlRepresentation.conditionalUpdate world)

theorem selectedStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolHorizon.selected (3+extra) (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.ok Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue,Solidity.Yul.Checks.LocalBoolControlRepresentation.state Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue world) := by
  intro world extra
  have observed : Solidity.Yul.LocalBoolControl.eval selected 3 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.ok Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue,Solidity.Yul.Checks.LocalBoolControlRepresentation.state Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue world) := rfl
  have terminal : (Solidity.Yul.LocalBoolControl.eval selected 3 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world)).1 ≠ .error .timeout := by
    rw [observed]
    intro impossible
    cases impossible
  exact (Solidity.Yul.LocalBoolHorizon.extension _ _ _ _ 3 extra _ terminal).trans observed

theorem unselectedTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env), Solidity.Yul.LocalBoolControl.eval (.not (.not (.not Solidity.Yul.Checks.LocalBoolControlRepresentation.read))) 2 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.error .timeout,(Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world)) := by
  intro world
  rfl

theorem partialRetained : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.fault 3 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.error .timeout,Solidity.Yul.Checks.LocalBoolControlRepresentation.state Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue world) := by
  exact Solidity.Yul.Checks.LocalBoolControlRepresentation.partialTimeout

theorem timeoutMayChange : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.fault 3 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) ≠ Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.fault 5 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) := by
  intro world same
  have final : Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.fault 5 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) =
      (.ok Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanFalse,Solidity.Yul.Checks.LocalBoolControlRepresentation.state Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue world) := rfl
  have results := congrArg (fun run => run.1) same
  rw [partialRetained,final] at results
  cases results

theorem dirtyProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env) (extra : Nat), (Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.orProof (2+extra) (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world)).1.map Solidity.Yul.LocalValue.clean? = .ok none := by
  intro world extra
  rw [orStable]
  rfl

theorem unsupportedCompare : ¬ Nonempty (Solidity.Yul.LocalBoolControl.Supported Solidity.Yul.Checks.LocalBoolControlRepresentation.env [.bool] (.compare .eq (.bool true) (.bool false))) := by
  intro witness
  rcases witness with ⟨proof⟩
  cases proof with
  | base child => cases child

#print axioms Solidity.Yul.LocalBoolHorizon.baseSuccessor
#print axioms Solidity.Yul.LocalBoolHorizon.successor
#print axioms Solidity.Yul.LocalBoolHorizon.extension
#print axioms andStable
#print axioms orStable
#print axioms conditionalStable
#print axioms selectedStable
#print axioms unselectedTimeout
#print axioms partialRetained
#print axioms timeoutMayChange
#print axioms dirtyProjection
#print axioms unsupportedCompare

end Solidity.Yul.Checks.LocalBoolHorizon
