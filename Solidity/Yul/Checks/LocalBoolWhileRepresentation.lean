import Solidity.Yul.LocalBoolWhileRepresentation
import Solidity.Yul.Checks.LocalBoolScopeRepresentation

namespace Solidity.Yul.Checks.LocalBoolWhileRepresentation
export Solidity.Yul.Checks.LocalBoolScopeRepresentation
  (env state raw cleanTrue cleanFalse read stop setFalse extended)
def body : Solidity.Source.RItems env [] false ⟨true,false⟩ [.bool] [.bool,.bool] :=
  .stmt (.declInit (τ := .bool) (.local .here) (by rfl))
    (.stmt (.expr (.assign (.local .here) (.unary .not (.local .here)))) .nil)
def proof : LocalBoolItems.Supported env [] false ⟨true,false⟩ body :=
  .declaration (.base (.local .here))
    (.expression (.assign .here (.not (.base (.local .here)))) .nil)
def statement : Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool] :=
  .whileLoop (.local .here) (.block body)
def witness : Nonempty (Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool]) :=
  ⟨statement⟩
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalBoolWhileRepresentation.whileLoop env [] false false
    [.bool] [.bool,.bool] (.local .here) read body proof fuel one two related

theorem whileFalse : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolWhileRepresentation.env), Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhileRepresentation.stop Solidity.Yul.Checks.LocalBoolWhileRepresentation.proof 5 (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world) := by
  intro world; rfl

theorem doFalseHalt : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolWhileRepresentation.env), Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolWhileRepresentation.stop Solidity.Yul.Checks.LocalBoolWhileRepresentation.proof 5 (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolWhileRepresentation.extended world) := by
  intro world; rfl

theorem doFalseComplete : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolWhileRepresentation.env), Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolWhileRepresentation.stop Solidity.Yul.Checks.LocalBoolWhileRepresentation.proof 8 (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world) := by
  intro world; rfl

theorem whileRecursion : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolWhileRepresentation.env), Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhileRepresentation.read Solidity.Yul.Checks.LocalBoolWhileRepresentation.proof 8 (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolWhileRepresentation.extended world) := by
  intro world; rfl

theorem doRecursion : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolWhileRepresentation.env), Solidity.Yul.LocalBoolDoWhile.run Solidity.Yul.Checks.LocalBoolWhileRepresentation.read Solidity.Yul.Checks.LocalBoolWhileRepresentation.proof 8 (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolWhileRepresentation.extended world) := by
  intro world; rfl

theorem guardWrite : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolWhileRepresentation.env), Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhileRepresentation.setFalse Solidity.Yul.Checks.LocalBoolWhileRepresentation.proof 3 (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state Solidity.Yul.Checks.LocalBoolWhileRepresentation.cleanFalse world) := by
  intro world; rfl

theorem zeroFuel : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolWhileRepresentation.env), Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhileRepresentation.read Solidity.Yul.Checks.LocalBoolWhileRepresentation.proof 0 (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world) := by
  intro world; rfl

theorem projectionRefused : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolWhileRepresentation.env), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalBoolWhile.run Solidity.Yul.Checks.LocalBoolWhileRepresentation.stop Solidity.Yul.Checks.LocalBoolWhileRepresentation.proof 5 (Solidity.Yul.Checks.LocalBoolWhileRepresentation.state (Solidity.Yul.Checks.LocalBoolWhileRepresentation.raw 2) world)) = none := by
  intro world; rfl

#print axioms Solidity.Yul.LocalBoolWhileRepresentation.whileLoop
#print axioms Solidity.Yul.LocalBoolWhileRepresentation.doWhileLoop
#print axioms whileFalse
#print axioms doFalseHalt
#print axioms doFalseComplete
#print axioms whileRecursion
#print axioms doRecursion
#print axioms guardWrite
#print axioms zeroFuel
#print axioms projectionRefused

end Solidity.Yul.Checks.LocalBoolWhileRepresentation
