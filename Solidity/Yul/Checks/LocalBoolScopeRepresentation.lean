import Solidity.Yul.LocalBoolScopeRepresentation
import Solidity.Yul.Checks.LocalBoolItemRepresentation

namespace Solidity.Yul.Checks.LocalBoolScopeRepresentation
export Solidity.Yul.Checks.LocalBoolItemRepresentation
  (env state raw cleanTrue cleanFalse body proof extended finalState)
def read : LocalBoolControl.Supported env [.bool] (.local .here) := .base (.local .here)
def stop : LocalBoolControl.Supported env [.bool] (.bool false) := .base (.literal false)
def setFalse : LocalBoolControl.Supported env [.bool] (.assign (.local .here) (.bool false)) :=
  .assign .here (.base (.literal false))
def statement : Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool] :=
  .ifThen (.local .here) (.block body)
def witness : Nonempty (Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool]) :=
  ⟨statement⟩
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalBoolScopeRepresentation.conditional
    env [] false ⟨false,false⟩ [.bool] [.bool,.bool] body proof
    (.local .here) read fuel one two related

theorem scopeCompletion : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolScopeRepresentation.env), Solidity.Yul.LocalBoolItemScope.run Solidity.Yul.Checks.LocalBoolScopeRepresentation.proof 7 (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) := by
  intro world; rfl

theorem scopeHaltRetainsContext : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolScopeRepresentation.env), Solidity.Yul.LocalBoolItemScope.run Solidity.Yul.Checks.LocalBoolScopeRepresentation.proof 4 (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolScopeRepresentation.extended world) := by
  intro world; rfl

theorem skippedBranch : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolScopeRepresentation.env), Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolScopeRepresentation.stop Solidity.Yul.Checks.LocalBoolScopeRepresentation.proof 2 (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) := by
  intro world; rfl

theorem takenBranch : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolScopeRepresentation.env), Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolScopeRepresentation.read Solidity.Yul.Checks.LocalBoolScopeRepresentation.proof 8 (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) := by
  intro world; rfl

theorem takenHaltRetainsContext : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolScopeRepresentation.env), Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolScopeRepresentation.read Solidity.Yul.Checks.LocalBoolScopeRepresentation.proof 5 (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolScopeRepresentation.extended world) := by
  intro world; rfl

theorem guardWriteRetained : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolScopeRepresentation.env), Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolScopeRepresentation.setFalse Solidity.Yul.Checks.LocalBoolScopeRepresentation.proof 3 (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state Solidity.Yul.Checks.LocalBoolScopeRepresentation.cleanFalse world) := by
  intro world; rfl

theorem dirtyProjectionRefused : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolScopeRepresentation.env), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolScopeRepresentation.read Solidity.Yul.Checks.LocalBoolScopeRepresentation.proof 8 (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world)) = none := by
  intro world; rfl

theorem zeroFuel : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolScopeRepresentation.env), Solidity.Yul.LocalBoolIf.run Solidity.Yul.Checks.LocalBoolScopeRepresentation.read Solidity.Yul.Checks.LocalBoolScopeRepresentation.proof 0 (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolScopeRepresentation.state (Solidity.Yul.Checks.LocalBoolScopeRepresentation.raw 2) world) := by
  intro world; rfl

#print axioms Solidity.Yul.LocalBoolScopeRepresentation.drop
#print axioms Solidity.Yul.LocalBoolScopeRepresentation.cast
#print axioms Solidity.Yul.LocalBoolScopeRepresentation.restore
#print axioms Solidity.Yul.LocalBoolScopeRepresentation.close
#print axioms Solidity.Yul.LocalBoolScopeRepresentation.scope
#print axioms Solidity.Yul.LocalBoolScopeRepresentation.conditional
#print axioms scopeCompletion
#print axioms scopeHaltRetainsContext
#print axioms skippedBranch
#print axioms takenBranch
#print axioms takenHaltRetainsContext
#print axioms guardWriteRetained
#print axioms dirtyProjectionRefused
#print axioms zeroFuel

end Solidity.Yul.Checks.LocalBoolScopeRepresentation
