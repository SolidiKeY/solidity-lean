import Solidity.Yul.LocalIfHorizon
import Solidity.Yul.Checks.LocalDefaultControlRepresentation

namespace Solidity.Yul.Checks.LocalIfHorizon
def emptyItems : Solidity.Source.RItems LocalDefaultControlRepresentation.env [] false
    ⟨false,false⟩ [.bool] [.bool] := .nil
def emptyProof : LocalDefaultItems.Supported LocalDefaultControlRepresentation.env [] false
    ⟨false,false⟩ emptyItems := .body .nil
def witness : Nonempty (LocalDefaultItems.Supported LocalDefaultControlRepresentation.env [] false
    ⟨false,false⟩ emptyItems) := ⟨emptyProof⟩


theorem yesStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env) (extra : Nat), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) (6+extra) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) := by
  intro world extra
  have completed : Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) := by rfl
  exact Solidity.Yul.LocalIfHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ _ 6 extra _ _ completed

theorem noStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env) (extra : Nat), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) (6+extra) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 0) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 0) world) := by
  intro world extra
  have completed : Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 0) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 0) world) := by rfl
  exact Solidity.Yul.LocalIfHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ _ 6 extra _ _ completed

theorem writeStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env) (extra : Nat), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.setFalse (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) (6+extra) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state Solidity.Yul.Checks.LocalDefaultControlRepresentation.cleanFalse world) := by
  intro world extra
  have completed : Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.setFalse (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state Solidity.Yul.Checks.LocalDefaultControlRepresentation.cleanFalse world) := by rfl
  exact Solidity.Yul.LocalIfHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ _ 6 extra _ _ completed

theorem selectedOnly : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env) (extra : Nat), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesGuard Solidity.Yul.Checks.LocalIfHorizon.emptyProof (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) (3+extra) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) := by
  intro world extra
  have completed : Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesGuard Solidity.Yul.Checks.LocalIfHorizon.emptyProof (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 3 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) := by rfl
  exact Solidity.Yul.LocalIfHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ _ 3 extra _ _ completed

theorem unselectedTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultItems.blockRun (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 2 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) := by
  intro world
  rfl

theorem yesTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesReached (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) := by
  intro world
  rfl

theorem noTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 0) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noReached (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 0) world) := by
  intro world
  rfl

theorem timeoutMayChange : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) ≠ Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) := by
  intro world same
  rw [yesTimeout,yesStable world 0] at same
  cases same

theorem dirtyProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) (6+extra) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world)) = none := by
  intro world extra
  rw [yesStable]
  rfl

theorem zeroTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 0 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 2) world) := by
  intro world
  rfl

#print axioms Solidity.Yul.LocalIfHorizon.successor
#print axioms Solidity.Yul.LocalIfHorizon.extension
#print axioms yesStable
#print axioms noStable
#print axioms writeStable
#print axioms selectedOnly
#print axioms unselectedTimeout
#print axioms yesTimeout
#print axioms noTimeout
#print axioms timeoutMayChange
#print axioms dirtyProjection
#print axioms zeroTimeout

end Solidity.Yul.Checks.LocalIfHorizon
