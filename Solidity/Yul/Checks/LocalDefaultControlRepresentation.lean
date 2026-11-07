import Solidity.Yul.LocalDefaultControlRepresentation
import Solidity.Yul.Checks.LocalBoolControlRepresentation

namespace Solidity.Yul.Checks.LocalDefaultControlRepresentation
export Solidity.Yul.Checks.LocalBoolControlRepresentation
  (env state raw cleanFalse read)
def stop : LocalBoolControl.Supported env [.bool] (.bool false) := .base (.literal false)
def yesGuard : LocalBoolControl.Supported env [.bool] (.bool true) := .base (.literal true)
def setFalse : LocalBoolControl.Supported env [.bool] (.assign (.local .here) (.bool false)) :=
  .assign .here (.base (.literal false))
def zero8 := RawDefaultDeclaration.intDefault env Solidity.Source.IntTy.u8
def zero256 := RawDefaultDeclaration.intDefault env Solidity.Source.IntTy.u256
abbrev YesOut : Solidity.Source.RCtx := [.int Solidity.Source.IntTy.u8,.bool]
abbrev NoOut : Solidity.Source.RCtx := [.int Solidity.Source.IntTy.u256,.bool]
def body (control : Solidity.Source.SCtx) (ty : Solidity.Source.STy) :
    Solidity.Source.RItems env [] false control [.bool] (ty :: [.bool]) :=
  .stmt (.declVar ty) (.stmt (.expr (.local (.there .here))) .nil)
def certified (control : Solidity.Source.SCtx) {ty : Solidity.Source.STy}
    (value : RawDefaultDeclaration.Default env ty) :
    LocalDefaultItems.Supported env [] false control (body control ty) :=
  .declaration value (.body (.expression (.base (.local (.there .here))) .nil))
def yesItems (control : Solidity.Source.SCtx) :
    Solidity.Source.RItems env [] false control [.bool] YesOut := body control (.int Solidity.Source.IntTy.u8)
def noItems (control : Solidity.Source.SCtx) :
    Solidity.Source.RItems env [] false control [.bool] NoOut := body control (.int Solidity.Source.IntTy.u256)
def yesProof (control : Solidity.Source.SCtx) :
    LocalDefaultItems.Supported env [] false control (yesItems control) := certified control zero8
def noProof (control : Solidity.Source.SCtx) :
    LocalDefaultItems.Supported env [] false control (noItems control) := certified control zero256
def yesReached (value : LocalValue env .bool) (world : Solidity.Source.St env) :
    LocalState env YesOut := ((.clean zero8.value,(value,())),world)
def noReached (value : LocalValue env .bool) (world : Solidity.Source.St env) :
    LocalState env NoOut := ((.clean zero256.value,(value,())),world)
def statement : Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool] :=
  .ifElse (.local .here) (.block (yesItems ⟨false,false⟩)) (.block (noItems ⟨false,false⟩))
def witness : Nonempty (Solidity.Source.RStmt env [] false ⟨false,false⟩ [.bool] [.bool]) :=
  ⟨statement⟩
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalDefaultControlRepresentation.ifElse env [] false ⟨false,false⟩
    [.bool] YesOut NoOut (.local .here) read (yesItems ⟨false,false⟩)
    (yesProof ⟨false,false⟩) (noItems ⟨false,false⟩) (noProof ⟨false,false⟩)
    fuel one two related

theorem yesBranchHalt : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesReached (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) := by

  intro world; rfl

theorem noBranchHalt : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 0) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noReached (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 0) world) := by

  intro world; rfl

theorem prefixTypesDistinct : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), ¬ Solidity.Yul.LocalBoolItemRepresentation.Items Solidity.Yul.Checks.LocalDefaultControlRepresentation.env [.bool] (Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesGuard (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world)) (Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.stop (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world)) := by

  intro world related
  change Solidity.Yul.LocalBoolItemRepresentation.Items _ _
    (.halted .timeout (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesReached (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world))
    (.halted .timeout (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noReached (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world)) at related
  cases related

theorem yesScopeClose : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) := by

  intro world; rfl

theorem noScopeClose : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 0) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 0) world) := by

  intro world; rfl

theorem guardWriteRetained : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.setFalse (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state Solidity.Yul.Checks.LocalDefaultControlRepresentation.cleanFalse world) := by

  intro world; rfl

theorem whileFalse : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.stop (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨true,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) := by

  intro world; rfl

theorem doFalseHalt : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.stop (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨true,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesReached (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) := by

  intro world; rfl

theorem doFalseCompletion : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultDoWhile.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.stop (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨true,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) = .normal (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) := by

  intro world; rfl

theorem loopRecursion : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨true,false⟩) 7 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesReached (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world) := by

  intro world; rfl

theorem dirtyProjectionRefused : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultControlRepresentation.env), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalDefaultIfElse.run Solidity.Yul.Checks.LocalDefaultControlRepresentation.read (Solidity.Yul.Checks.LocalDefaultControlRepresentation.yesProof ⟨false,false⟩) (Solidity.Yul.Checks.LocalDefaultControlRepresentation.noProof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultControlRepresentation.state (Solidity.Yul.Checks.LocalDefaultControlRepresentation.raw 1) world)) = none := by

  intro world; rfl

#print axioms Solidity.Yul.LocalDefaultControlRepresentation.ifElse
#print axioms Solidity.Yul.LocalDefaultControlRepresentation.whileLoop
#print axioms Solidity.Yul.LocalDefaultControlRepresentation.doWhileLoop
#print axioms yesBranchHalt
#print axioms noBranchHalt
#print axioms prefixTypesDistinct
#print axioms yesScopeClose
#print axioms noScopeClose
#print axioms guardWriteRetained
#print axioms whileFalse
#print axioms doFalseHalt
#print axioms doFalseCompletion
#print axioms loopRecursion
#print axioms dirtyProjectionRefused

end Solidity.Yul.Checks.LocalDefaultControlRepresentation
