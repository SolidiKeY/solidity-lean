import Solidity.Yul.LocalForInitHorizon
import Solidity.Yul.Checks.LocalBoolForPostRepresentation

/-! Full-for context growth, restoration and partial-frame horizon controls. -/
namespace Solidity.Yul.Checks.LocalForInitHorizon

theorem counterStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.setCounterFalse Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof (9+extra) (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) := by
  intro world extra
  exact Solidity.Yul.LocalForInitHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ _ _ 9 extra _ _ (Solidity.Yul.Checks.LocalBoolForPostRepresentation.counterWriteScoped world)

theorem initializerStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.setFalse Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.fault Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof (4+extra) (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state Solidity.Yul.Checks.LocalBoolForPostRepresentation.cleanFalse world) := by
  intro world extra
  exact Solidity.Yul.LocalForInitHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 extra _ _ (Solidity.Yul.Checks.LocalBoolForPostRepresentation.initializerWrite world)

theorem skippedStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.stop Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.fault Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof (3+extra) (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) := by
  intro world extra
  exact Solidity.Yul.LocalForInitHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 extra _ _ (Solidity.Yul.Checks.LocalBoolForPostRepresentation.skippedPost world)

theorem initializerTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolInitialization.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read 1 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) := by
  intro world
  rfl

theorem initializerFrame : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolInitialization.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read 2 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolForRepresentation.afterInit world) := by
  intro world
  rfl

theorem scopeAgreement : ∀ (fuel : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolItemScope.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof fuel (Solidity.Yul.Checks.LocalBoolForRepresentation.afterInit world) = Solidity.Yul.LocalDefaultItems.blockRun (.body Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof) fuel (Solidity.Yul.Checks.LocalBoolForRepresentation.afterInit world) := by
  intro fuel world
  exact Solidity.Yul.LocalForInitHorizon.scope_agrees _ _ _ _ _ _ _ _ fuel _

theorem iterationAgreement : ∀ (fuel : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolPostIter.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.setCounterFalse Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof fuel (Solidity.Yul.Checks.LocalBoolForRepresentation.afterInit world) = Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.setCounterFalse (.body Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof) fuel (Solidity.Yul.Checks.LocalBoolForRepresentation.afterInit world) := by
  intro fuel world
  exact Solidity.Yul.LocalForInitHorizon.iteration_agrees _ _ _ _ _ _ _ _ _ _ _ _ fuel _

theorem bodyBeforePost : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.setCounterFalse Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 6 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForPostRepresentation.afterBody world) := by
  intro world
  rfl

theorem postKeepsFrame : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.fault Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 9 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForPostRepresentation.afterPostWrite world) := by
  exact Solidity.Yul.Checks.LocalBoolForPostRepresentation.postHaltKeepsFrame

theorem dirtyProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env) (extra : Nat), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.setCounterFalse Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof (9+extra) (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world)) = none := by
  intro world extra
  rw [counterStable]
  rfl

theorem timeoutChanges : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.setCounterFalse Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 6 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) ≠ Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.setCounterFalse Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 9 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) := by
  intro world same
  rw [bodyBeforePost,counterStable world 0] at same
  cases same

#print axioms Solidity.Yul.LocalForInitHorizon.scope_agrees
#print axioms Solidity.Yul.LocalForInitHorizon.initializerSuccessor
#print axioms Solidity.Yul.LocalForInitHorizon.iteration_agrees
#print axioms Solidity.Yul.LocalForInitHorizon.iterationSuccessor
#print axioms Solidity.Yul.LocalForInitHorizon.successor
#print axioms Solidity.Yul.LocalForInitHorizon.extension
#print axioms counterStable
#print axioms initializerStable
#print axioms skippedStable
#print axioms initializerTimeout
#print axioms initializerFrame
#print axioms scopeAgreement
#print axioms iterationAgreement
#print axioms bodyBeforePost
#print axioms postKeepsFrame
#print axioms dirtyProjection
#print axioms timeoutChanges

end Solidity.Yul.Checks.LocalForInitHorizon
