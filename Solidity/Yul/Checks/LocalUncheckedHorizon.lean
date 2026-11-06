import Solidity.Yul.LocalUncheckedHorizon
import Solidity.Yul.Checks.LocalDefaultRepresentation
import Solidity.Yul.Checks.LocalBoolControlRepresentation

namespace Solidity.Yul.Checks.LocalUncheckedHorizon
def faultItems : Solidity.Source.RItems LocalDefaultRepresentation.env [] false ⟨false,false⟩
    [.bool] [.bool] :=
  .stmt (.expr LocalBoolControlRepresentation.faultExpr) .nil
def faultTail : LocalDefaultItems.Supported LocalDefaultRepresentation.env [] false
    ⟨false,false⟩ faultItems :=
  .body (.expression LocalBoolControlRepresentation.fault .nil)
def witness : Nonempty (LocalDefaultItems.Supported LocalDefaultRepresentation.env [] false
    ⟨false,false⟩ faultItems) := ⟨faultTail⟩


theorem completedObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.full (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world
  rfl

theorem completedStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env) (extra : Nat), Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) (6+extra) (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.full (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world extra
  exact Solidity.Yul.LocalUncheckedHorizon.extension _ _ _ _ _ _ _ _ _ _ _ 6 extra _ _ (completedObserved world)

theorem blockObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultUnchecked.blockRun (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 7 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world
  rfl

theorem blockStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env) (extra : Nat), Solidity.Yul.LocalDefaultUnchecked.blockRun (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) (7+extra) (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world extra
  exact Solidity.Yul.LocalUncheckedHorizon.blockExtension _ _ _ _ _ _ _ _ _ _ _ 7 extra _ _ (blockObserved world)

theorem innerPrefixTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 4 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultRepresentation.first (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world
  rfl

theorem innerFullTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultRepresentation.full (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world
  rfl

theorem continuationTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) Solidity.Yul.Checks.LocalUncheckedHorizon.faultTail 6 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultRepresentation.initial Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue world) := by
  intro world
  rfl

theorem continuationCompleted : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) Solidity.Yul.Checks.LocalUncheckedHorizon.faultTail 8 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.initial Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue world) := by
  intro world
  rfl

theorem continuationStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env) (extra : Nat), Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) Solidity.Yul.Checks.LocalUncheckedHorizon.faultTail (8+extra) (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.initial Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue world) := by
  intro world extra
  exact Solidity.Yul.LocalUncheckedHorizon.extension _ _ _ _ _ _ _ _ _ _ _ 8 extra _ _ (continuationCompleted world)

theorem timeoutMayChange : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) ≠ Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world) := by
  intro world same
  rw [innerFullTimeout,completedObserved] at same
  cases same

theorem dirtyProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalDefaultUnchecked.blockRun (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) (7+extra) (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 2) world)) = none := by
  intro world extra
  rw [blockStable]
  rfl

#print axioms Solidity.Yul.LocalUncheckedHorizon.successor
#print axioms Solidity.Yul.LocalUncheckedHorizon.extension
#print axioms Solidity.Yul.LocalUncheckedHorizon.blockSuccessor
#print axioms Solidity.Yul.LocalUncheckedHorizon.blockExtension
#print axioms completedObserved
#print axioms completedStable
#print axioms blockObserved
#print axioms blockStable
#print axioms innerPrefixTimeout
#print axioms innerFullTimeout
#print axioms continuationTimeout
#print axioms continuationCompleted
#print axioms continuationStable
#print axioms timeoutMayChange
#print axioms dirtyProjection

end Solidity.Yul.Checks.LocalUncheckedHorizon
