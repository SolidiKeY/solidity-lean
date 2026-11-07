import Solidity.Yul.LocalBoolForRepresentation
import Solidity.Yul.Checks.LocalBoolWhileRepresentation

namespace Solidity.Yul.Checks.LocalBoolForRepresentation
export Solidity.Yul.Checks.LocalBoolWhileRepresentation
  (env state raw cleanTrue cleanFalse read stop setFalse)
def test : LocalBoolControl.Supported env [.bool,.bool] (.local .here) :=
  .base (.local .here)
def writeOuter : LocalBoolControl.Supported env [.bool,.bool]
    (.assign (.local (.there .here)) (.bool false)) :=
  .assign (.there .here) (.base (.literal false))
def body : Solidity.Source.RItems env [] false ⟨true,false⟩ [.bool,.bool] [.bool,.bool,.bool] :=
  .stmt (.declInit (τ := .bool) (.local .here) (by rfl))
    (.stmt (.expr (.assign (.local .here) (.unary .not (.local .here)))) .nil)
def proof : LocalBoolItems.Supported env [] false ⟨true,false⟩ body :=
  .declaration (.base (.local .here))
    (.expression (.assign .here (.not (.base (.local .here)))) .nil)
def afterInit (world : Solidity.Source.St env) : LocalState env [.bool,.bool] :=
  ((raw 2,(raw 2,())),world)
def afterBody (world : Solidity.Source.St env) : LocalState env [.bool,.bool,.bool] :=
  ((raw 2,(raw 2,(raw 2,()))),world)
def statement : Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool] :=
  .forLoop (.declInit (τ := .bool) (.local .here) (by rfl))
    (.some (.local .here)) .none (.block body)
def witness : Nonempty (Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool]) :=
  ⟨statement⟩
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalBoolForRepresentation.forLoop env [] false false
    [.bool] [.bool,.bool,.bool] (.local .here) read
    (.local .here) test body proof fuel one two related

theorem normalClosure : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForRepresentation.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolForRepresentation.stop Solidity.Yul.Checks.LocalBoolForRepresentation.test Solidity.Yul.Checks.LocalBoolForRepresentation.proof 3 (Solidity.Yul.Checks.LocalBoolForRepresentation.state (Solidity.Yul.Checks.LocalBoolForRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolForRepresentation.state (Solidity.Yul.Checks.LocalBoolForRepresentation.raw 2) world) := by
  intro world; rfl

theorem initializerWrite : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForRepresentation.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolForRepresentation.setFalse Solidity.Yul.Checks.LocalBoolForRepresentation.test Solidity.Yul.Checks.LocalBoolForRepresentation.proof 4 (Solidity.Yul.Checks.LocalBoolForRepresentation.state (Solidity.Yul.Checks.LocalBoolForRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolForRepresentation.state Solidity.Yul.Checks.LocalBoolForRepresentation.cleanFalse world) := by
  intro world; rfl

theorem guardWrite : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForRepresentation.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolForRepresentation.read Solidity.Yul.Checks.LocalBoolForRepresentation.writeOuter Solidity.Yul.Checks.LocalBoolForRepresentation.proof 5 (Solidity.Yul.Checks.LocalBoolForRepresentation.state (Solidity.Yul.Checks.LocalBoolForRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolForRepresentation.state Solidity.Yul.Checks.LocalBoolForRepresentation.cleanFalse world) := by
  intro world; rfl

theorem beforeInitialization : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForRepresentation.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolForRepresentation.read Solidity.Yul.Checks.LocalBoolForRepresentation.test Solidity.Yul.Checks.LocalBoolForRepresentation.proof 2 (Solidity.Yul.Checks.LocalBoolForRepresentation.state (Solidity.Yul.Checks.LocalBoolForRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForRepresentation.state (Solidity.Yul.Checks.LocalBoolForRepresentation.raw 2) world) := by
  intro world; rfl

theorem afterInitialization : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForRepresentation.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolForRepresentation.read Solidity.Yul.Checks.LocalBoolForRepresentation.test Solidity.Yul.Checks.LocalBoolForRepresentation.proof 3 (Solidity.Yul.Checks.LocalBoolForRepresentation.state (Solidity.Yul.Checks.LocalBoolForRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForRepresentation.afterInit world) := by
  intro world; rfl

theorem bodyHalt : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForRepresentation.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolForRepresentation.read Solidity.Yul.Checks.LocalBoolForRepresentation.test Solidity.Yul.Checks.LocalBoolForRepresentation.proof 6 (Solidity.Yul.Checks.LocalBoolForRepresentation.state (Solidity.Yul.Checks.LocalBoolForRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForRepresentation.afterBody world) := by
  intro world; rfl

theorem recursiveHalt : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForRepresentation.env), Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolForRepresentation.read Solidity.Yul.Checks.LocalBoolForRepresentation.test Solidity.Yul.Checks.LocalBoolForRepresentation.proof 10 (Solidity.Yul.Checks.LocalBoolForRepresentation.state (Solidity.Yul.Checks.LocalBoolForRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolForRepresentation.afterBody world) := by
  intro world; rfl

theorem dirtyProjectionRefused : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolForRepresentation.env), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalBoolFor.run Solidity.Yul.Checks.LocalBoolForRepresentation.stop Solidity.Yul.Checks.LocalBoolForRepresentation.test Solidity.Yul.Checks.LocalBoolForRepresentation.proof 3 (Solidity.Yul.Checks.LocalBoolForRepresentation.state (Solidity.Yul.Checks.LocalBoolForRepresentation.raw 2) world)) = none := by
  intro world; rfl

#print axioms Solidity.Yul.LocalBoolForRepresentation.close
#print axioms Solidity.Yul.LocalBoolForRepresentation.forLoop
#print axioms normalClosure
#print axioms initializerWrite
#print axioms guardWrite
#print axioms beforeInitialization
#print axioms afterInitialization
#print axioms bodyHalt
#print axioms recursiveHalt
#print axioms dirtyProjectionRefused

end Solidity.Yul.Checks.LocalBoolForRepresentation
