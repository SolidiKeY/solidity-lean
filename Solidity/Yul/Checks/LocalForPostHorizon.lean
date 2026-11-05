import Solidity.Yul.LocalForPostHorizon
import Solidity.Yul.Checks.LocalWhileHorizon

namespace Solidity.Yul.Checks.LocalForPostHorizon
export LocalDefaultControlRepresentation
  (env state raw cleanFalse read stop setFalse yesGuard yesProof yesReached)
def slowExpr : Solidity.Source.RExpr env [.bool] .bool :=
  .unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.local .here))))))
def slow : LocalBoolControl.Supported env [.bool] slowExpr :=
  .not (.not (.not (.not (.not (.not (.base (.local .here)))))))
def faultExpr : Solidity.Source.RExpr env [.bool] .bool :=
  .binary .or (.assign (.local .here) (.bool false)) slowExpr
def postFault : LocalBoolControl.Supported env [.bool] faultExpr := .or setFalse slow
def witness : Nonempty (LocalBoolControl.Supported env [.bool] faultExpr) := ⟨postFault⟩


theorem completedObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.setFalse (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) 6 (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForPostHorizon.state Solidity.Yul.Checks.LocalForPostHorizon.cleanFalse world) := by
  intro world
  rfl

theorem completedStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env) (extra : Nat), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.setFalse (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) (6+extra) (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForPostHorizon.state Solidity.Yul.Checks.LocalForPostHorizon.cleanFalse world) := by
  intro world extra
  exact Solidity.Yul.LocalForPostHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ 6 extra _ _ (completedObserved world)

theorem bodyFailure : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.postFault (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) 5 (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalForPostHorizon.yesReached (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) := by
  intro world
  rfl

theorem postFailure : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.postFault (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) 6 (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalForPostHorizon.state Solidity.Yul.Checks.LocalForPostHorizon.cleanFalse world) := by
  intro world
  rfl

theorem postRecoveryStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env) (extra : Nat), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.postFault (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) (9+extra) (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForPostHorizon.state Solidity.Yul.Checks.LocalForPostHorizon.cleanFalse world) := by
  intro world extra
  have completed : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.postFault (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) 9 (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForPostHorizon.state Solidity.Yul.Checks.LocalForPostHorizon.cleanFalse world) := by rfl
  exact Solidity.Yul.LocalForPostHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ 9 extra _ _ completed

theorem timeoutMayChange : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.postFault (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) 6 (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) ≠ Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.postFault (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) 9 (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) := by
  intro world same
  rw [postFailure,postRecoveryStable world 0] at same
  cases same

theorem falseGuardSkipsBoth : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env) (extra : Nat), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.stop Solidity.Yul.Checks.LocalForPostHorizon.postFault (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) (2+extra) (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) := by
  intro world extra
  have completed : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.stop Solidity.Yul.Checks.LocalForPostHorizon.postFault (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) 2 (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) := by rfl
  exact Solidity.Yul.LocalForPostHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ 2 extra _ _ completed

theorem postFalseStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env) (extra : Nat), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.stop Solidity.Yul.Checks.LocalWhileHorizon.body (10+extra) (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForPostHorizon.state Solidity.Yul.Checks.LocalForPostHorizon.cleanFalse world) := by
  intro world extra
  have completed : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.stop Solidity.Yul.Checks.LocalWhileHorizon.body 10 (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForPostHorizon.state Solidity.Yul.Checks.LocalForPostHorizon.cleanFalse world) := by rfl
  exact Solidity.Yul.LocalForPostHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ 10 extra _ _ completed

theorem postTrueStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env) (extra : Nat), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.yesGuard Solidity.Yul.Checks.LocalWhileHorizon.body (10+extra) (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForPostHorizon.state Solidity.Yul.Checks.LocalForPostHorizon.cleanFalse world) := by
  intro world extra
  have completed : Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.yesGuard Solidity.Yul.Checks.LocalWhileHorizon.body 10 (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalForPostHorizon.state Solidity.Yul.Checks.LocalForPostHorizon.cleanFalse world) := by rfl
  exact Solidity.Yul.LocalForPostHorizon.extension _ _ _ _ _ _ _ _ _ _ _ _ 10 extra _ _ completed

theorem dirtyProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env) (extra : Nat), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.stop Solidity.Yul.Checks.LocalForPostHorizon.postFault (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) (2+extra) (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world)) = none := by
  intro world extra
  rw [falseGuardSkipsBoth]
  rfl

theorem zeroTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalForPostHorizon.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalForPostHorizon.read Solidity.Yul.Checks.LocalForPostHorizon.postFault (Solidity.Yul.Checks.LocalForPostHorizon.yesProof ⟨true,false⟩) 0 (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalForPostHorizon.state (Solidity.Yul.Checks.LocalForPostHorizon.raw 2) world) := by
  intro world
  rfl

#print axioms Solidity.Yul.LocalForPostHorizon.successor
#print axioms Solidity.Yul.LocalForPostHorizon.extension
#print axioms completedObserved
#print axioms completedStable
#print axioms bodyFailure
#print axioms postFailure
#print axioms postRecoveryStable
#print axioms timeoutMayChange
#print axioms falseGuardSkipsBoth
#print axioms postFalseStable
#print axioms postTrueStable
#print axioms dirtyProjection
#print axioms zeroTimeout

end Solidity.Yul.Checks.LocalForPostHorizon
