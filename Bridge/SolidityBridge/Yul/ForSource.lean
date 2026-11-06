import SolidityBridge.Yul.LoweredWhile
import Solidity.Yul.ClosedHorizon
namespace SolidityBridge.Yul.ForSource
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

/-! Shared proof over the original evaluator. The two normal-source laws are
real premises, concretely discharged by each consuming compiler. No source
AST/state/evaluator, target convention or proof budget is introduced. -/

include afterCorrect insideCorrect in
theorem source_loop (base count : Nat) (hc : cf ≤ base) (hp : pf ≤ base) (hb : bf ≤ base)
    (locals : Vector Scalar.Word n)
    (running : ∀ j, j < count → test.value (Nat.repeat (fun l => after (inside l)) j locals) ≠ 0)
    (stopped : test.value (Nat.repeat (fun l => after (inside l)) count locals) = 0) :
    evalLoop (base+(count+1)) (c := c) .nil True.intro condition test.profile
      post afterProfile body insideProfile (sourceLocals locals) =
      some ⟨sourceLocals (Nat.repeat (fun l => after (inside l)) count locals),.normal⟩ := by
  induction count generalizing locals with
  | zero =>
    have testRun := evalExpr_stable hc .nil True.intro condition test.profile
      (sourceLocals locals) (test.source locals)
    change test.value locals = 0 at stopped
    rw [evalLoop,testRun]
    rw [stopped]
    rfl
  | succ count ih =>
    have testRun := evalExpr_stable (show cf ≤ base+(count+1) by omega) .nil True.intro
      condition test.profile (sourceLocals locals) (test.source locals)
    have bodyRun := evalStmt_stable (show bf ≤ base+(count+1) by omega) .nil True.intro
      body insideProfile (sourceLocals locals) (insideCorrect locals)
    have postRun := evalStmt_stable (show pf ≤ base+(count+1) by omega) .nil True.intro
      post afterProfile (sourceLocals (inside locals)) (afterCorrect (inside locals))
    have nonzero : (test.value locals).toNat ≠ 0 := by
      intro zero
      exact running 0 (by omega) (BitVec.eq_of_toNat_eq zero)
    rw [Nat.add_succ,evalLoop,testRun]
    change (if (test.value locals).toNat = 0 then _ else _) = _
    rw [if_neg nonzero]
    change (evalStmt (base+(count+1)) .nil True.intro body insideProfile
      (sourceLocals locals)).bind _ = _
    rw [bodyRun]
    change (evalStmt (base+(count+1)) .nil True.intro post afterProfile
      (sourceLocals (inside locals))).bind _ = _
    rw [postRun]
    change evalLoop (base+(count+1)) .nil True.intro condition test.profile
      post afterProfile body insideProfile (sourceLocals (after (inside locals))) = _
    have restRunning : ∀ j, j < count →
        test.value (Nat.repeat (fun l => after (inside l)) j
          (after (inside locals))) ≠ 0 := by
      intro j bound
      rw [LoweredWhile.repeat_shift]
      exact running (j+1) (by omega)
    have restStopped : test.value (Nat.repeat (fun l => after (inside l)) count
        (after (inside locals))) = 0 := by
      rw [LoweredWhile.repeat_shift]
      exact stopped
    have rest := ih (after (inside locals)) restRunning restStopped
    rw [LoweredWhile.repeat_shift] at rest
    exact rest

/-- info: 'SolidityBridge.Yul.ForSource.source_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_loop
end
end SolidityBridge.Yul.ForSource
