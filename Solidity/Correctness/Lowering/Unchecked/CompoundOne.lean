import Solidity.Correctness.Lowering.Unchecked.IntegerOne
import Solidity.Correctness.Lowering.Unchecked.IntegerUpdate
import Solidity.Source.Eval

/-!
# Compound-one evaluation for integer lvalues

Guards duplication or reordering of an effectful lvalue when comparing the
Source meanings of compound-one and prefix increment/decrement. The integer
value law uses the intrinsic Source value type, not an extra success or range
assumption on a location read. Raw rewriting and target lvalue capture remain
separate obligations.
-/
namespace Solidity.Correctness.Lowering.Unchecked

/-- Every value at an integer type supports the shared update identity.
Impossible reference constructors are eliminated by their location proofs;
no well-typed integer value or arithmetic panic is excluded. -/
theorem integerValueUpdate {D : Source.Layout} (t : Source.IntTy)
    (checked inc : Bool) (value : Source.Val D (.int t)) :
    Source.binVal checked (if inc then .add else .sub) value
      (.int 1 (integerOne_range t)) = Source.incDecVal checked inc value := by
  cases value with
  | int x range => exact integerUpdate t checked inc x range
  | memRef h _ => cases h
  | storRef h _ => cases h
  | cdRef h _ _ => cases h

/-- The actual Source computations agree for every integer lvalue, including
its effects and failures. The RHS literal is evaluated and converted exactly;
location evaluation and reading are then shared, never assumed successful.
This compares both operations in the same checkedness context, not checked
execution with unchecked execution. All horizons and failure plans remain. -/
theorem compoundOne_eval {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (t : Source.IntTy) (inc : Bool) (l : Source.RLVal E Γ (.int t))
    (fits : (if inc then Source.AssignOp.add else .sub).fits E.isBase E.mapFree
      (.rational (Source.Q.ofInt 1)) (.int t) = true) :
    Source.evalE G F horizon
      (.compound (if inc then .add else .sub) l (.const (Source.Q.ofInt 1)) fits)
      (plan := plan) (calldataKnown := known) =
    Source.evalE G F horizon (.incDec inc true l)
      (plan := plan) (calldataKnown := known) := by
  have guard {α : Type} (action : Source.EM E Γ α) :
      Source.withLibraryCalldata known (.int t) action = action := by
    cases known <;> rfl
  have convert (n : Nat) : Source.convRV (E := E) (Γ := Γ) F n (.int t) (.const (Source.Q.ofInt 1)) =
      pure (.val (.int 1 (integerOne_range t))) := by
    change (do
      let value ← Source.EM.lift (E := E) (Γ := Γ)
        (Source.constVal (D := E.layout) (Source.Q.ofInt 1) (.int t))
      pure (Source.RVal.val value)) = _
    rw [constantOne]
    rfl
  have getValue : Source.getV (E := E) (Γ := Γ) (.val (.int 1 (integerOne_range t))) =
      pure (.int 1 (integerOne_range t)) := rfl
  have kind : (if inc then Source.AssignOp.add else .sub).kind? = some .arith := by
    cases inc <;> rfl
  have operator : (if inc then Source.AssignOp.add else .sub).binOp =
      (if inc then Source.BinOp.add else .sub) := by
    cases inc <;> rfl
  cases horizon with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => cases known <;> rfl
    | succ fuel =>
      have rhsAction : Source.evalE (Γ := Γ) G F (fuel + 1) (.const (Source.Q.ofInt 1))
          (plan := plan) (calldataKnown := known) = pure (.const (Source.Q.ofInt 1)) := by
        cases known <;> rfl
      rw [Source.evalE, Source.evalE]
      simp only [guard, rhsAction, pure_bind, kind, convert, getValue, operator,
        integerValueUpdate, if_true]

#print axioms integerValueUpdate
#print axioms compoundOne_eval

end Solidity.Correctness.Lowering.Unchecked
