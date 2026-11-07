import Solidity.Optimizer.Controls

namespace H62.OptimizerMigration
open Solidity.Optimizer

-- Every proposal is safe for scalar equality, at every input.
example (proposal : Pass Nat) (n : Nat) :
    validated (Validator.equality Nat) proposal n = n :=
  Eq.symm (validated_preserves (fun _ => rfl) (Validator.equality Nat) proposal n)

-- Mixed accept/reject stages must use the current input and preserve order.
example : guardedPipeline (Validator.equality Nat) [Nat.succ, id, fun n => n + 2] 37 = 37 := rfl
example : Pass.pipeline [Nat.succ, fun n => n * 2] 3 = 8 := rfl
example : Pass.pipeline [fun n => n * 2, Nat.succ] 3 = 7 := rfl

-- Intrinsic control and local indices cannot be changed by pass coercion.
example : True := by
  fail_if_success
    have bad : Solidity.Yul.Stmt [] [] ⟨true, false⟩ 0 := Controls.yulWitness
  fail_if_success
    have bad : Solidity.Yul.Stmt [] [] ⟨false, false⟩ 1 := Controls.yulWitness
  exact True.intro

-- The pipeline proof must retain transitivity; equality is the tested instance.
example (ps : List (Pass Nat)) :
    Preserves Eq (guardedPipeline (Validator.equality Nat) ps) :=
  guardedPipeline_preserves (fun _ => rfl) (fun a b => a.trans b)
    (Validator.equality Nat) ps
end H62.OptimizerMigration
