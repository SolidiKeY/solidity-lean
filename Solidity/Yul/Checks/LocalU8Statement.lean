import Solidity.Yul.LocalU8Statement
import Solidity.Yul.Checks.LocalU8Representation
namespace Solidity.Yul.Checks.LocalU8Statement
def witness : Nonempty (LocalU8Expr.Supported LocalU8Representation.env LocalU8Representation.Ctx LocalU8Representation.orderExpr) := ⟨LocalU8Representation.order⟩
theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalU8Representation.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalU8Representation.env)) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx) (locals : Solidity.Source.Locals Solidity.Yul.Checks.LocalU8Representation.env.layout Solidity.Yul.Checks.LocalU8Representation.Ctx)
 (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env),
 Solidity.Yul.LocalExprStatement.project (Solidity.Yul.LocalU8Statement.run Solidity.Yul.Checks.LocalU8Representation.order glob.pipeline fuel (Solidity.Yul.LocalState.ofClean (locals,world))) =
 some ((Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.expr (R:=returns) (M:=modifier) (k:=control) Solidity.Yul.Checks.LocalU8Representation.orderExpr) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.LocalU8Representation.env,world)) := by
  intro glob frame checked fuel nps ph returns modifier control locals world
  exact Solidity.Yul.LocalU8Statement.source_agrees Solidity.Yul.Checks.LocalU8Representation.env Solidity.Yul.Checks.LocalU8Representation.Ctx Solidity.Yul.Checks.LocalU8Representation.orderExpr Solidity.Yul.Checks.LocalU8Representation.order glob frame checked fuel nps ph returns modifier control locals world

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalU8Statement.run Solidity.Yul.Checks.LocalU8Representation.timeout .legacy 5 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error .timeout,(Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro world
  rfl

theorem viaPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalU8Statement.run Solidity.Yul.Checks.LocalU8Representation.timeout .viaIR 5 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) = (.error .timeout,(Solidity.Yul.Checks.LocalU8Representation.initial 2 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) := by
  intro world
  rfl

theorem rawAssignment : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.LocalU8Statement.run Solidity.Yul.Checks.LocalU8Representation.assign pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 2 257 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 = .ok () ∧ (Solidity.Yul.Checks.LocalU8Representation.word8 ((Solidity.Yul.LocalU8Statement.run Solidity.Yul.Checks.LocalU8Representation.assign pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 2 257 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).2.1.get Solidity.Yul.Checks.LocalU8Representation.x)).val = 257 ∧ (Solidity.Yul.LocalU8Statement.run Solidity.Yul.Checks.LocalU8Representation.assign pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 2 257 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).2.1.get Solidity.Yul.Checks.LocalU8Representation.flag = Solidity.Yul.Checks.LocalU8Representation.rawBool ∧ Solidity.Yul.LocalExprStatement.project (Solidity.Yul.LocalU8Statement.run Solidity.Yul.Checks.LocalU8Representation.assign pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 2 257 Solidity.Yul.Checks.LocalU8Representation.rawBool world)) = none := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem overflow : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), (Solidity.Yul.LocalU8Statement.run Solidity.Yul.Checks.LocalU8Representation.sum pipeline 4 (Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1 = .error (.revert (Solidity.Source.panicData .arithmetic)) := by
  intro pipeline world
  change (Solidity.Yul.LocalU8Expr.eval Solidity.Yul.Checks.LocalU8Representation.sum pipeline 3 (Solidity.Yul.Checks.LocalU8Representation.initial 511 1 Solidity.Yul.Checks.LocalU8Representation.rawBool world)).1.map (fun _ => ()) = _
  rw [Solidity.Yul.Checks.LocalU8Representation.overflow]
  rfl

theorem zeroRead : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.LocalU8Representation.env), Solidity.Yul.LocalU8Statement.run Solidity.Yul.Checks.LocalU8Representation.readX pipeline 0 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) ≠ Solidity.Yul.LocalU8Statement.run Solidity.Yul.Checks.LocalU8Representation.readX pipeline 2 (Solidity.Yul.Checks.LocalU8Representation.initial 257 2 Solidity.Yul.Checks.LocalU8Representation.rawBool world) := by
  intro pipeline world bad
  have tags := congrArg Prod.fst bad
  cases tags

theorem unsupportedSub : ¬ Nonempty (Solidity.Yul.LocalU8Expr.Supported Solidity.Yul.Checks.LocalU8Representation.env Solidity.Yul.Checks.LocalU8Representation.Ctx (.binary .sub (.local Solidity.Yul.Checks.LocalU8Representation.x) (.local Solidity.Yul.Checks.LocalU8Representation.arg))) := by
  exact Solidity.Yul.Checks.LocalU8Representation.unsupportedSub

theorem checkedBoundary : Solidity.Source.binVal true .add (Solidity.Source.Val.int (D := Solidity.Yul.Checks.LocalU8Representation.env.layout) (t := Solidity.Source.IntTy.u8) 255 (by decide)) (Solidity.Source.Val.int (D := Solidity.Yul.Checks.LocalU8Representation.env.layout) (t := Solidity.Source.IntTy.u8) 1 (by decide)) ≠ Solidity.Source.binVal false .add (Solidity.Source.Val.int (D := Solidity.Yul.Checks.LocalU8Representation.env.layout) (t := Solidity.Source.IntTy.u8) 255 (by decide)) (Solidity.Source.Val.int (D := Solidity.Yul.Checks.LocalU8Representation.env.layout) (t := Solidity.Source.IntTy.u8) 1 (by decide)) := by
  intro bad
  cases bad

#print axioms Solidity.Yul.LocalU8Statement.zero
#print axioms Solidity.Yul.LocalU8Statement.step
#print axioms Solidity.Yul.LocalU8Statement.source_agrees
#print axioms sourceAll
#print axioms legacyPartial
#print axioms viaPartial
#print axioms rawAssignment
#print axioms overflow
#print axioms zeroRead
#print axioms unsupportedSub
#print axioms checkedBoundary
end Solidity.Yul.Checks.LocalU8Statement
