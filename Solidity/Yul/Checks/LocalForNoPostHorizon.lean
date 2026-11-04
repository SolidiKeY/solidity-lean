import Solidity.Yul.LocalForNoPostHorizon
import Solidity.Yul.Checks.LocalBoolForRepresentation

namespace Solidity.Yul.Checks.LocalForNoPostHorizon
export LocalBoolForRepresentation (env state raw cleanFalse read stop setFalse test afterInit afterBody)
abbrev Out : Solidity.Source.RCtx := [.bool,.bool,.bool]
def counter : Solidity.Source.Idx Out .bool := .there .here
def outer : Solidity.Source.Idx Out .bool := .there (.there .here)
def items : Solidity.Source.RItems env [] false ⟨true,false⟩ [.bool,.bool] Out :=
  .stmt (.declInit (τ := .bool) (.local .here) (by rfl))
    (.stmt (.expr (.assign (.local counter) (.bool false)))
      (.stmt (.expr (.assign (.local outer) (.bool false))) .nil))
def body : LocalBoolItems.Supported env [] false ⟨true,false⟩ items :=
  .declaration (.base (.local .here))
    (.expression (.assign counter (.base (.literal false)))
      (.expression (.assign outer (.base (.literal false))) .nil))
def witness : Nonempty (LocalBoolItems.Supported env [] false ⟨true,false⟩ items) := ⟨body⟩
def counterChanged (world : Solidity.Source.St env) : LocalState env Out :=
  ((raw 2,(cleanFalse,(raw 2,()))),world)


theorem completedObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.read Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body 9 (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForNoPostHorizon.state Solidity.Yul.Checks.LocalForNoPostHorizon.cleanFalse world) := by
  intro world
  rfl

theorem completedStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env) (extra : Nat), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.read Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body (9+extra) (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForNoPostHorizon.state Solidity.Yul.Checks.LocalForNoPostHorizon.cleanFalse world) := by
  intro world extra
  exact Solidity.Yul.LocalForNoPostHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ 9 extra _ _ (completedObserved world)

theorem initializerRetained : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.read Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body 3 (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalForNoPostHorizon.afterInit world) := by
  intro world
  rfl

theorem bodyPrefix : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.read Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body 7 (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalForNoPostHorizon.afterBody world) := by
  intro world
  rfl

theorem counterWritten : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.read Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body 8 (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalForNoPostHorizon.counterChanged world) := by
  intro world
  rfl

theorem timeoutChanges : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.read Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body 8 (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) ≠ Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.read Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body 9 (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) := by
  intro world same
  rw [counterWritten,completedObserved] at same
  cases same

theorem stoppedStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env) (extra : Nat), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.stop Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body (3+extra) (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) := by
  intro world extra
  have completed : Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.stop Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body 3 (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) := by rfl
  exact Solidity.Yul.LocalForNoPostHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ 3 extra _ _ completed

theorem initializerWriteStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env) (extra : Nat), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.setFalse Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body (4+extra) (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForNoPostHorizon.state Solidity.Yul.Checks.LocalForNoPostHorizon.cleanFalse world) := by
  intro world extra
  have completed : Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.setFalse Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body 4 (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForNoPostHorizon.state Solidity.Yul.Checks.LocalForNoPostHorizon.cleanFalse world) := by rfl
  exact Solidity.Yul.LocalForNoPostHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ 4 extra _ _ completed

theorem scopeAgreement : ∀ (fuel : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env), Solidity.Yul.LocalBoolItemScope.run Solidity.Yul.Checks.LocalForNoPostHorizon.body fuel (Solidity.Yul.Checks.LocalForNoPostHorizon.afterInit world) = Solidity.Yul.LocalDefaultItems.blockRun (.body Solidity.Yul.Checks.LocalForNoPostHorizon.body) fuel (Solidity.Yul.Checks.LocalForNoPostHorizon.afterInit world) := by
  intro fuel world
  exact Solidity.Yul.LocalForInitHorizon.scope_agrees _ _ _ _ _ _ _ _ fuel _

theorem whileAgreement : ∀ (fuel : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env), Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body fuel (Solidity.Yul.Checks.LocalForNoPostHorizon.afterInit world) = Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalForNoPostHorizon.test (.body Solidity.Yul.Checks.LocalForNoPostHorizon.body) fuel (Solidity.Yul.Checks.LocalForNoPostHorizon.afterInit world) := by
  intro fuel world
  exact Solidity.Yul.LocalForNoPostHorizon.iteration_agrees _ _ _ _ _ _ _ _ _ _ fuel _

theorem dirtyProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env) (extra : Nat), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.stop Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body (3+extra) (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world)) = none := by
  intro world extra
  rw [stoppedStable]
  rfl

theorem zeroTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForNoPostHorizon.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalForNoPostHorizon.read Solidity.Yul.Checks.LocalForNoPostHorizon.test Solidity.Yul.Checks.LocalForNoPostHorizon.body 0 (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalForNoPostHorizon.state (Solidity.Yul.Checks.LocalForNoPostHorizon.raw 2) world) := by
  intro world
  rfl

#print axioms Solidity.Yul.LocalForNoPostHorizon.iteration_agrees
#print axioms Solidity.Yul.LocalForNoPostHorizon.iterationSuccessor
#print axioms Solidity.Yul.LocalForNoPostHorizon.successor
#print axioms Solidity.Yul.LocalForNoPostHorizon.extension
#print axioms completedObserved
#print axioms completedStable
#print axioms initializerRetained
#print axioms bodyPrefix
#print axioms counterWritten
#print axioms timeoutChanges
#print axioms stoppedStable
#print axioms initializerWriteStable
#print axioms scopeAgreement
#print axioms whileAgreement
#print axioms dirtyProjection
#print axioms zeroTimeout

end Solidity.Yul.Checks.LocalForNoPostHorizon
