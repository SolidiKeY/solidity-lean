import Solidity.Correctness.Lowering.Unchecked.IntegerUpdate
import Solidity.Source.Eval
import Solidity.Source.Hoare

/-!
# Shared local compound-one and prefix update

Guards a discrepancy between compound-one and increment/decrement at the
actual Source evaluation boundary, including checked arithmetic failures and
their poststates. Both expressions use local lvalues; the right operand is a
local containing one, not an arbitrary effectful expression. This ingredient
does not certify raw spelling, a literal conversion, target code, or a pass.
-/
namespace Solidity.Correctness.Lowering.Unchecked

/-- One stateful Source law for addition/increment and subtraction/decrement.
Both sides use the same frame, pipeline, checkedness, failure plan, calldata
mode and initial interpreter state, and produce equal complete results and
poststates.
`fits` is the resolved constructor's static typing evidence. The read premises
are concrete local values; they are not whole-execution correctness oracles.
No premise bounds the updated value or excludes a panic. -/
theorem localCompoundOne {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (source : Source.EMState E Γ) (t : Source.IntTy) (inc : Bool)
    (i j : Source.Idx Γ (.int t)) (x : Int)
    (range : t.lo ≤ x ∧ x ≤ t.hi) (oneRange : t.lo ≤ 1 ∧ 1 ≤ t.hi)
    (read : source.1.get i = .int x range)
    (readOne : source.1.get j = .int 1 oneRange)
    (fits : (if inc then Source.AssignOp.add else .sub).fits E.isBase E.mapFree
      (.int t) (.int t) = true) :
    (Source.evalE G F (fuel + 2)
      (.compound (if inc then .add else .sub) (.local i) (.local j) fits)
      (plan := plan) (calldataKnown := known)).run source =
    (Source.evalE G F (fuel + 2) (.incDec inc true (.local i))
      (plan := plan) (calldataKnown := known)).run source := by
  have guard {α : Type} (action : Source.EM E Γ α) :
      Source.withLibraryCalldata known (.int t) action = action := by
    cases known <;> rfl
  have rhsRun : (Source.evalE G F (fuel + 1) (.local j)
      (plan := plan) (calldataKnown := known)).run source =
      (.ok (.val (.int 1 oneRange)), source) := by
    rw [Source.evalE, guard]
    change ((Except.ok (.val (source.1.get j)) : Source.R (Source.RVal E.layout (.int t))), source) = _
    rw [readOne]
  have locRun : (Source.evalLoc G F (fuel + 1) (.local i)
      (plan := plan) (calldataKnown := known)).run source =
      (.ok (.local i), source) := rfl
  have oldRun : (Source.readLoc F (.local i)).run source =
      (.ok (.int x range), source) := by
    change ((Except.ok (source.1.get i) : Source.R (Source.Val E.layout (.int t))), source) = _
    rw [read]
  have convRun : (Source.convRV F (fuel + 1) (.int t)
      (.val (.int 1 oneRange))).run source =
      (.ok (.val (.int 1 oneRange)), source) := by
    simp only [Source.convRV]
    rfl
  have getRun : (Source.getV (.val (.int 1 oneRange))).run source =
      (.ok (.int 1 oneRange), source) := rfl
  have kind : (if inc then Source.AssignOp.add else .sub).kind? = some .arith := by
    cases inc <;> rfl
  have operator : (if inc then Source.AssignOp.add else .sub).binOp =
      (if inc then Source.BinOp.add else .sub) := by
    cases inc <;> rfl
  have arithmetic : Source.binVal F.checked
      (if inc then Source.AssignOp.add else .sub).binOp
      (.int x range : Source.Val E.layout (.int t)) (.int 1 oneRange) =
      Source.incDecVal F.checked inc (.int x range) := by
    simpa only [operator] using integerUpdate (D := E.layout) t F.checked inc x range
  rw [Source.evalE, Source.evalE]
  simp only [guard]
  rw [Source.Hoare.run_bind, rhsRun]
  dsimp only
  simp only [Source.Hoare.run_bind, locRun, oldRun]
  simp only [kind, Source.Hoare.run_bind, convRun, getRun, if_true]
  rw [arithmetic]

#print axioms localCompoundOne

end Solidity.Correctness.Lowering.Unchecked
