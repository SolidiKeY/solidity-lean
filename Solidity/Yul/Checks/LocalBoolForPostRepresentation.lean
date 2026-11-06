import Solidity.Yul.LocalBoolForPostRepresentation
import Solidity.Yul.Checks.LocalBoolForRepresentation

namespace Solidity.Yul.Checks.LocalBoolForPostRepresentation
export Solidity.Yul.Checks.LocalBoolForRepresentation
  (env state raw cleanTrue cleanFalse read stop setFalse test writeOuter body proof afterBody)
def yes : LocalBoolControl.Supported env [.bool,.bool] (.bool true) := .base (.literal true)
def no : LocalBoolControl.Supported env [.bool,.bool] (.bool false) := .base (.literal false)
def setCounterFalse : LocalBoolControl.Supported env [.bool,.bool]
    (.assign (.local .here) (.bool false)) :=
  .assign .here (.base (.literal false))
def faultExpr : Solidity.Source.RExpr env [.bool,.bool] .bool :=
  .binary .and (.assign (.local (.there .here)) (.bool true)) (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.local .here)))))))))
def fault : LocalBoolControl.Supported env [.bool,.bool] faultExpr :=
  .and (.assign (.there .here) (.base (.literal true))) (.not (.not (.not (.not (.not (.not (.not (.not (.base (.local .here))))))))))
def afterBodyWrite (world : Solidity.Source.St env) : LocalState env [.bool,.bool,.bool] :=
  ((raw 2,(raw 2,(cleanFalse,()))),world)
def afterPostWrite (world : Solidity.Source.St env) : LocalState env [.bool,.bool] :=
  ((raw 2,(cleanTrue,())),world)
def statement : Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool] :=
  .forLoop (.declInit (τ := .bool) (.local .here) (by rfl))
    (.some (.local .here)) (.some faultExpr) (.block body)
def witness : Nonempty (Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool]) :=
  ⟨statement⟩
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalBoolForPostRepresentation.forLoop env [] false false
    [.bool] [.bool,.bool,.bool] (.local .here) read
    (.local .here) faultExpr test fault body proof fuel one two related

theorem counterWriteScoped : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.setCounterFalse Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 9 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) := by
  intro world; rfl

theorem outerPostWrite : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.writeOuter Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 9 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForPostRepresentation.afterBodyWrite world) := by
  intro world; rfl

theorem falsePostIgnored : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.no Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 9 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForPostRepresentation.afterBody world) := by
  intro world; rfl

theorem truePostIgnored : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.yes Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 9 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForPostRepresentation.afterBody world) := by
  intro world; rfl

theorem skippedPost : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.stop Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.fault Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 3 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) := by
  intro world; rfl

theorem initializerWrite : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.setFalse Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.fault Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 4 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state Solidity.Yul.Checks.LocalBoolForPostRepresentation.cleanFalse world) := by
  intro world; rfl

theorem bodyBeforePost : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.fault Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 6 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForPostRepresentation.afterBody world) := by
  intro world; rfl

theorem postHaltKeepsFrame : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.fault Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 9 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForPostRepresentation.afterPostWrite world) := by
  intro world; rfl

theorem dirtyProjectionRefused : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForPostRepresentation.env), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalBoolForPost.run Solidity.Yul.Checks.LocalBoolForPostRepresentation.read Solidity.Yul.Checks.LocalBoolForPostRepresentation.test Solidity.Yul.Checks.LocalBoolForPostRepresentation.setCounterFalse Solidity.Yul.Checks.LocalBoolForPostRepresentation.proof 9 (Solidity.Yul.Checks.LocalBoolForPostRepresentation.state (Solidity.Yul.Checks.LocalBoolForPostRepresentation.raw 2) world)) = none := by
  intro world; rfl

#print axioms Solidity.Yul.LocalBoolForPostRepresentation.forLoop
#print axioms counterWriteScoped
#print axioms outerPostWrite
#print axioms falsePostIgnored
#print axioms truePostIgnored
#print axioms skippedPost
#print axioms initializerWrite
#print axioms bodyBeforePost
#print axioms postHaltKeepsFrame
#print axioms dirtyProjectionRefused

end Solidity.Yul.Checks.LocalBoolForPostRepresentation
