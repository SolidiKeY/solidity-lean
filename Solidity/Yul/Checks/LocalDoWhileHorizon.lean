import Solidity.Yul.LocalDoWhileHorizon
import Solidity.Yul.Checks.LocalWhileHorizon

namespace Solidity.Yul.Checks.LocalDoWhileHorizon
export LocalWhileHorizon (env state raw cleanFalse read stop Ty Out zero flag reached)
def toggleItems : Solidity.Source.RItems env [] false ⟨true,false⟩ [.bool] Out :=
  .stmt (.declVar Ty)
    (.stmt (.expr (.assign (.local flag) (.unary .not (.local flag)))) .nil)
def toggleBody : LocalDefaultItems.Supported env [] false ⟨true,false⟩ toggleItems :=
  .declaration zero (.body
    (.expression (.assign flag (.not (.base (.local flag)))) .nil))
def witness : Nonempty (LocalDefaultItems.Supported env [] false ⟨true,false⟩ toggleItems) :=
  ⟨toggleBody⟩


theorem existingBodyObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.read Solidity.Yul.Checks.LocalWhileHorizon.body 10 (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDoWhileHorizon.state Solidity.Yul.Checks.LocalDoWhileHorizon.cleanFalse world) := by
  intro world
  rfl

theorem existingBodyStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env) (extra : Nat), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.read Solidity.Yul.Checks.LocalWhileHorizon.body (10+extra) (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDoWhileHorizon.state Solidity.Yul.Checks.LocalDoWhileHorizon.cleanFalse world) := by
  intro world extra
  exact Solidity.Yul.LocalDoWhileHorizon.extension _ _ _ _ _ _ _ _ _ _ 10 extra _ _ (existingBodyObserved world)

theorem falseGuardStillExecutes : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env) (extra : Nat), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.stop Solidity.Yul.Checks.LocalWhileHorizon.body (10+extra) (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDoWhileHorizon.state Solidity.Yul.Checks.LocalDoWhileHorizon.cleanFalse world) := by
  intro world extra
  have completed : Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.stop Solidity.Yul.Checks.LocalWhileHorizon.body 10 (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalDoWhileHorizon.state Solidity.Yul.Checks.LocalDoWhileHorizon.cleanFalse world) := by rfl
  exact Solidity.Yul.LocalDoWhileHorizon.extension _ _ _ _ _ _ _ _ _ _ 10 extra _ _ completed

theorem toggleCompleted : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.read Solidity.Yul.Checks.LocalDoWhileHorizon.toggleBody 9 (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 0) world) = .normal (Solidity.Yul.Checks.LocalDoWhileHorizon.state Solidity.Yul.Checks.LocalDoWhileHorizon.cleanFalse world) := by
  intro world
  rfl

theorem toggleStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env) (extra : Nat), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.read Solidity.Yul.Checks.LocalDoWhileHorizon.toggleBody (9+extra) (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 0) world) = .normal (Solidity.Yul.Checks.LocalDoWhileHorizon.state Solidity.Yul.Checks.LocalDoWhileHorizon.cleanFalse world) := by
  intro world extra
  exact Solidity.Yul.LocalDoWhileHorizon.extension _ _ _ _ _ _ _ _ _ _ 9 extra _ _ (toggleCompleted world)

theorem secondIterationTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.read Solidity.Yul.Checks.LocalDoWhileHorizon.toggleBody 8 (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 0) world) = .halted .timeout (Solidity.Yul.Checks.LocalDoWhileHorizon.reached Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue world) := by
  intro world
  rfl

theorem firstPrefixTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.read Solidity.Yul.Checks.LocalDoWhileHorizon.toggleBody 6 (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 0) world) = .halted .timeout (Solidity.Yul.Checks.LocalDoWhileHorizon.reached (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 0) world) := by
  intro world
  rfl

theorem timeoutMayChange : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.read Solidity.Yul.Checks.LocalDoWhileHorizon.toggleBody 8 (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 0) world) ≠ Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.read Solidity.Yul.Checks.LocalDoWhileHorizon.toggleBody 9 (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 0) world) := by
  intro world same
  rw [secondIterationTimeout,toggleCompleted] at same
  cases same

theorem zeroTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.read Solidity.Yul.Checks.LocalDoWhileHorizon.toggleBody 0 (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 0) world) = .halted .timeout (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 0) world) := by
  intro world
  rfl

theorem literalTrueNeverCompletes : ∀ (fuel : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env) (next : Solidity.Yul.LocalState Solidity.Yul.Checks.LocalDoWhileHorizon.env [.bool]), Solidity.Yul.LocalDefaultDoWhile.run (.base (.literal true)) Solidity.Yul.Checks.LocalDoWhileHorizon.toggleBody fuel (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 0) world) ≠ .normal next := by
  intro fuel world next
  exact Solidity.Yul.LocalDefaultDoWhile.no_normal _ _ _ _ _ _ _ _ fuel _ _

theorem projectionAfterExplicitWrite : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDoWhileHorizon.env) (extra : Nat), (Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDoWhileHorizon.stop Solidity.Yul.Checks.LocalWhileHorizon.body (10+extra) (Solidity.Yul.Checks.LocalDoWhileHorizon.state (Solidity.Yul.Checks.LocalDoWhileHorizon.raw 2) world))).isSome = true := by
  intro world extra
  rw [falseGuardStillExecutes]
  rfl

#print axioms Solidity.Yul.LocalDoWhileHorizon.successor
#print axioms Solidity.Yul.LocalDoWhileHorizon.extension
#print axioms existingBodyObserved
#print axioms existingBodyStable
#print axioms falseGuardStillExecutes
#print axioms toggleCompleted
#print axioms toggleStable
#print axioms secondIterationTimeout
#print axioms firstPrefixTimeout
#print axioms timeoutMayChange
#print axioms zeroTimeout
#print axioms literalTrueNeverCompletes
#print axioms projectionAfterExplicitWrite

end Solidity.Yul.Checks.LocalDoWhileHorizon
