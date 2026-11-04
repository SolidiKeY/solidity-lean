import SolidityBridge.Yul.ForSource

/-! Shared original-evaluator completion induction. Normal source laws below
are real premises; concrete consumers must discharge them from their actual
compiler exports. This theorem alone is not compilation adequacy. -/
namespace SolidityBridge.Yul.ForCompletionSource
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions
section
variable {c : Solidity.Yul.Control} {n cf pf bf : Nat}
  {condition : Solidity.Yul.Expr [] [] n 1}
  {post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
  (test : ProducerExpressions.Compiled cf condition)
  (afterProfile : StmtWordP post) (after : Vector Scalar.Word n → Vector Scalar.Word n)
  (afterCorrect : ∀ locals, evalStmt pf .nil True.intro post afterProfile (sourceLocals locals) =
    some ⟨sourceLocals (after locals),.normal⟩)
  (insideProfile : StmtWordP body) (inside : Vector Scalar.Word n → Vector Scalar.Word n)
  (insideCorrect : ∀ locals, evalStmt bf .nil True.intro body insideProfile (sourceLocals locals) =
    some ⟨sourceLocals (inside locals),.normal⟩)

include afterCorrect insideCorrect in
theorem loop_complete (fuel : Nat) (locals : Vector Scalar.Word n) (out : Outcome c n)
    (completed : evalLoop fuel .nil True.intro condition test.profile post afterProfile
      body insideProfile (sourceLocals locals) = some out) :
    ∃ count, count < fuel ∧
      (∀ j, j < count → test.value (Nat.repeat (fun l => after (inside l)) j locals) ≠ 0) ∧
      test.value (Nat.repeat (fun l => after (inside l)) count locals) = 0 ∧
      out = ⟨sourceLocals (Nat.repeat (fun l => after (inside l)) count locals),.normal⟩ := by
  induction fuel generalizing locals with
  | zero => cases completed
  | succ fuel ih =>
    rw [evalLoop] at completed
    cases tested : evalExpr fuel .nil True.intro condition test.profile (sourceLocals locals) with
    | none => simp only [tested] at completed; cases completed
    | some values =>
      rw [tested] at completed
      have same := evalExpr_completed_unique .nil True.intro condition test.profile
        (sourceLocals locals) tested (test.source locals)
      subst values
      change (if (test.value locals).toNat = 0 then some ⟨sourceLocals locals,.normal⟩ else _) = some out at completed
      by_cases zero : test.value locals = 0
      · rw [zero] at completed
        change some ⟨sourceLocals locals,.normal⟩ = some out at completed
        exact ⟨0,by omega,(by intro j bound; omega),zero,(Option.some.inj completed).symm⟩
      · have nz : (test.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
        rw [if_neg nz] at completed
        change (evalStmt fuel .nil True.intro body insideProfile (sourceLocals locals)).bind _ = some out at completed
        cases bodyRun : evalStmt fuel .nil True.intro body insideProfile (sourceLocals locals) with
        | none => simp only [bodyRun] at completed; cases completed
        | some result =>
          rw [bodyRun] at completed
          have same := evalStmt_completed_unique .nil True.intro body insideProfile
            (sourceLocals locals) bodyRun (insideCorrect locals)
          subst result
          change (evalStmt fuel .nil True.intro post afterProfile
            (sourceLocals (inside locals))).bind _ = some out at completed
          cases postRun : evalStmt fuel .nil True.intro post afterProfile
              (sourceLocals (inside locals)) with
          | none => simp only [postRun] at completed; cases completed
          | some result =>
            rw [postRun] at completed
            have same := evalStmt_completed_unique .nil True.intro post afterProfile
              (sourceLocals (inside locals)) postRun (afterCorrect (inside locals))
            subst result
            change evalLoop fuel .nil True.intro condition test.profile post afterProfile
              body insideProfile (sourceLocals (after (inside locals))) = some out at completed
            obtain ⟨count,bound,running,stopped,result⟩ := ih (after (inside locals)) completed
            refine ⟨count+1,by omega,?_,?_,?_⟩
            · intro j prior
              cases j with
              | zero => exact zero
              | succ j =>
                rw [←LoweredWhile.repeat_shift]
                exact running j (by omega)
            · rw [←LoweredWhile.repeat_shift]
              exact stopped
            · rw [←LoweredWhile.repeat_shift]
              exact result

end
/-- info: 'SolidityBridge.Yul.ForCompletionSource.loop_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms loop_complete
end SolidityBridge.Yul.ForCompletionSource
