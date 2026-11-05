import Solidity.Yul.LocalBoolPostRepresentation
import Solidity.Yul.Checks.LocalBoolWhileRepresentation

namespace Solidity.Yul.Checks.LocalBoolPostRepresentation
export Solidity.Yul.Checks.LocalBoolWhileRepresentation
  (env state raw cleanTrue cleanFalse read stop setFalse body proof extended)
def yes : LocalBoolControl.Supported env [.bool] (.bool true) := .base (.literal true)
def setTrue : LocalBoolControl.Supported env [.bool] (.assign (.local .here) (.bool true)) :=
  .assign .here (.base (.literal true))
def faultExpr : Solidity.Source.RExpr env [.bool] .bool :=
  .binary .and (.assign (.local .here) (.bool true)) (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.unary .not (.local .here)))))))))
def fault : LocalBoolControl.Supported env [.bool] faultExpr :=
  .and setTrue (.not (.not (.not (.not (.not (.not (.not (.not read))))))))
def witness : Nonempty (LocalBoolControl.Supported env [.bool] faultExpr) := ⟨fault⟩
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalBoolPostRepresentation.postIter env [] false false
    [.bool] [.bool,.bool] (.local .here) (.assign (.local .here) (.bool false))
    read setFalse body proof fuel one two related

theorem postWriteStops : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolPostRepresentation.env), Solidity.Yul.LocalBoolPostIter.run Solidity.Yul.Checks.LocalBoolPostRepresentation.read Solidity.Yul.Checks.LocalBoolPostRepresentation.setFalse Solidity.Yul.Checks.LocalBoolPostRepresentation.proof 8 (Solidity.Yul.Checks.LocalBoolPostRepresentation.state (Solidity.Yul.Checks.LocalBoolPostRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolPostRepresentation.state Solidity.Yul.Checks.LocalBoolPostRepresentation.cleanFalse world) := by
  intro world; rfl

theorem falsePostIgnored : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolPostRepresentation.env), Solidity.Yul.LocalBoolPostIter.run Solidity.Yul.Checks.LocalBoolPostRepresentation.read Solidity.Yul.Checks.LocalBoolPostRepresentation.stop Solidity.Yul.Checks.LocalBoolPostRepresentation.proof 8 (Solidity.Yul.Checks.LocalBoolPostRepresentation.state (Solidity.Yul.Checks.LocalBoolPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolPostRepresentation.extended world) := by
  intro world; rfl

theorem truePostIgnored : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolPostRepresentation.env), Solidity.Yul.LocalBoolPostIter.run Solidity.Yul.Checks.LocalBoolPostRepresentation.read Solidity.Yul.Checks.LocalBoolPostRepresentation.yes Solidity.Yul.Checks.LocalBoolPostRepresentation.proof 8 (Solidity.Yul.Checks.LocalBoolPostRepresentation.state (Solidity.Yul.Checks.LocalBoolPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolPostRepresentation.extended world) := by
  intro world; rfl

theorem skippedPost : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolPostRepresentation.env), Solidity.Yul.LocalBoolPostIter.run Solidity.Yul.Checks.LocalBoolPostRepresentation.stop Solidity.Yul.Checks.LocalBoolPostRepresentation.fault Solidity.Yul.Checks.LocalBoolPostRepresentation.proof 2 (Solidity.Yul.Checks.LocalBoolPostRepresentation.state (Solidity.Yul.Checks.LocalBoolPostRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolPostRepresentation.state (Solidity.Yul.Checks.LocalBoolPostRepresentation.raw 2) world) := by
  intro world; rfl

theorem bodyHaltBeforePost : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolPostRepresentation.env), Solidity.Yul.LocalBoolPostIter.run Solidity.Yul.Checks.LocalBoolPostRepresentation.read Solidity.Yul.Checks.LocalBoolPostRepresentation.fault Solidity.Yul.Checks.LocalBoolPostRepresentation.proof 5 (Solidity.Yul.Checks.LocalBoolPostRepresentation.state (Solidity.Yul.Checks.LocalBoolPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolPostRepresentation.extended world) := by
  intro world; rfl

theorem postHaltKeepsWrite : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolPostRepresentation.env), Solidity.Yul.LocalBoolPostIter.run Solidity.Yul.Checks.LocalBoolPostRepresentation.read Solidity.Yul.Checks.LocalBoolPostRepresentation.fault Solidity.Yul.Checks.LocalBoolPostRepresentation.proof 8 (Solidity.Yul.Checks.LocalBoolPostRepresentation.state (Solidity.Yul.Checks.LocalBoolPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolPostRepresentation.state Solidity.Yul.Checks.LocalBoolPostRepresentation.cleanTrue world) := by
  intro world; rfl

theorem zeroFuel : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolPostRepresentation.env), Solidity.Yul.LocalBoolPostIter.run Solidity.Yul.Checks.LocalBoolPostRepresentation.read Solidity.Yul.Checks.LocalBoolPostRepresentation.fault Solidity.Yul.Checks.LocalBoolPostRepresentation.proof 0 (Solidity.Yul.Checks.LocalBoolPostRepresentation.state (Solidity.Yul.Checks.LocalBoolPostRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolPostRepresentation.state (Solidity.Yul.Checks.LocalBoolPostRepresentation.raw 2) world) := by
  intro world; rfl

theorem dirtyProjectionRefused : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolPostRepresentation.env), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalBoolPostIter.run Solidity.Yul.Checks.LocalBoolPostRepresentation.stop Solidity.Yul.Checks.LocalBoolPostRepresentation.fault Solidity.Yul.Checks.LocalBoolPostRepresentation.proof 2 (Solidity.Yul.Checks.LocalBoolPostRepresentation.state (Solidity.Yul.Checks.LocalBoolPostRepresentation.raw 2) world)) = none := by
  intro world; rfl

#print axioms Solidity.Yul.LocalBoolPostRepresentation.postIter
#print axioms postWriteStops
#print axioms falsePostIgnored
#print axioms truePostIgnored
#print axioms skippedPost
#print axioms bodyHaltBeforePost
#print axioms postHaltKeepsWrite
#print axioms zeroFuel
#print axioms dirtyProjectionRefused

end Solidity.Yul.Checks.LocalBoolPostRepresentation
