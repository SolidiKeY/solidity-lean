import Solidity.Correctness.Lowering.Unchecked.IntegerUpdate
import Solidity.Correctness.Lowering.Unchecked.IntegerOne
import Solidity.Source.Eval
import Solidity.Source.Hoare

/-!
# Shared local compound-one and prefix update

Guards a discrepancy between compound-one and increment/decrement at the
actual Source evaluation boundary, including checked arithmetic failures and
their poststates. Both expressions use local lvalues; the right operand is a
local containing one or the exact literal one, not an arbitrary effectful
expression. These ingredients do not certify raw spelling, target code, or a pass.
-/
namespace Solidity.Correctness.Lowering.Unchecked

/-- Private evaluator-step factorization. Its two evaluation equations are
proved by the public concrete specializations below, never accepted as a
validator's semantic-correctness oracle. -/
private theorem compoundOne_of_runs {E : Source.Env} {Γ : Source.RCtx} {σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (source : Source.EMState E Γ) (t : Source.IntTy) (inc : Bool)
    (i : Source.Idx Γ (.int t)) (rhs : Source.RExpr E Γ σ)
    (value : Source.RVal E.layout σ) (x : Int)
    (range : t.lo ≤ x ∧ x ≤ t.hi) (oneRange : t.lo ≤ 1 ∧ 1 ≤ t.hi)
    (read : source.1.get i = .int x range)
    (fits : (if inc then Source.AssignOp.add else .sub).fits E.isBase E.mapFree σ (.int t) = true)
    (rhsRun : (Source.evalE G F (fuel + 1) rhs
      (plan := plan) (calldataKnown := known)).run source = (.ok value, source))
    (convRun : (Source.convRV F (fuel + 1) (.int t) value).run source =
      (.ok (.val (.int 1 oneRange)), source)) :
    (Source.evalE G F (fuel + 2)
      (.compound (if inc then .add else .sub) (.local i) rhs fits)
      (plan := plan) (calldataKnown := known)).run source =
    (Source.evalE G F (fuel + 2) (.incDec inc true (.local i))
      (plan := plan) (calldataKnown := known)).run source := by
  have guard {α : Type} (action : Source.EM E Γ α) :
      Source.withLibraryCalldata known (.int t) action = action := by
    cases known <;> rfl
  have locRun : (Source.evalLoc G F (fuel + 1) (.local i)
      (plan := plan) (calldataKnown := known)).run source =
      (.ok (.local i), source) := rfl
  have oldRun : (Source.readLoc F (.local i)).run source =
      (.ok (.int x range), source) := by
    change ((Except.ok (source.1.get i) : Source.R (Source.Val E.layout (.int t))), source) = _
    rw [read]
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
  have convRun : (Source.convRV F (fuel + 1) (.int t)
      (.val (.int 1 oneRange))).run source =
      (.ok (.val (.int 1 oneRange)), source) := by
    simp only [Source.convRV]
    rfl
  exact compoundOne_of_runs G F fuel plan known source t inc i (.local j)
    (.val (.int 1 oneRange)) x range oneRange read fits rhsRun convRun

/-- A literal-one compound update and prefix increment/decrement have the
same complete Source result/poststate. This specialization proves both
literal evaluation and exact conversion; it accepts no execution equation.
The static `fits` proof is precisely the resolved constructor's field. This
is still a Source law, not certification of raw or emitted intrinsic syntax. -/
theorem literalCompoundOne {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (source : Source.EMState E Γ) (t : Source.IntTy) (inc : Bool)
    (i : Source.Idx Γ (.int t)) (x : Int) (range : t.lo ≤ x ∧ x ≤ t.hi)
    (read : source.1.get i = .int x range)
    (fits : (if inc then Source.AssignOp.add else .sub).fits E.isBase E.mapFree
      (.rational (Source.Q.ofInt 1)) (.int t) = true) :
    (Source.evalE G F (fuel + 2)
      (.compound (if inc then .add else .sub) (.local i) (.const (Source.Q.ofInt 1)) fits)
      (plan := plan) (calldataKnown := known)).run source =
    (Source.evalE G F (fuel + 2) (.incDec inc true (.local i))
      (plan := plan) (calldataKnown := known)).run source := by
  have rhsRun : (Source.evalE G F (fuel + 1) (.const (Source.Q.ofInt 1))
      (plan := plan) (calldataKnown := known)).run source =
      (.ok (.const (Source.Q.ofInt 1)), source) := by
    cases known <;> rfl
  have convRun : (Source.convRV F (fuel + 1) (.int t) (.const (Source.Q.ofInt 1))).run source =
      (.ok (.val (.int 1 (integerOne_range t))), source) := by
    change (do
      let value ← Source.EM.lift (E := E) (Γ := Γ)
        (Source.constVal (D := E.layout) (Source.Q.ofInt 1) (.int t))
      pure (Source.RVal.val value)).run source = _
    rw [constantOne]
    rfl
  exact compoundOne_of_runs G F fuel plan known source t inc i (.const (Source.Q.ofInt 1))
    (.const (Source.Q.ofInt 1)) x range (integerOne_range t) read fits rhsRun convRun

#print axioms localCompoundOne
#print axioms literalCompoundOne

end Solidity.Correctness.Lowering.Unchecked
