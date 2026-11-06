import Solidity.Evm.Machine

/-! G36.01 target selector over the existing EVM instruction semantics.
No new AST or source evaluator is introduced. The post-condition machine is
explicit: a condition prefix may have effects. G24 must separately supply the
actual condition/body compilation and representation facts at that machine.
Nonzero body skips are preserved, never silently interpreted as source return.
-/
namespace Solidity.Backend.StructuredFlow.Branch
open Solidity.Evm

/-- Existing relative-jump shape, with arbitrary already-emitted arm code. -/
def emit (condition left right : List Instr) : List Instr :=
  condition ++ ([.iszero, .jumpi (left.length + 1)] ++
    (left ++ ([.jump right.length] ++ right)))

/-- False selects the entire right outcome, including an escaping skip.
The skipped left arm cannot affect any field of the actual machine. -/
theorem false_run {condition left right : List Instr} {initial post : Machine}
    (test : run condition initial = .ok (post.push (.val (bword false))) 0) :
    run (emit condition left right) initial = run right post := by
  unfold emit
  rw [run_append_ok test]
  rw [run_append_skip (m' := post) (k := left.length + 1) rfl,
    exec_skip_append]
  rfl

/-- True executes the actual left code and retains its precise pending skip.
This law makes the continuation boundary visible to abrupt-control clients. -/
theorem true_run {condition left right : List Instr} {initial post : Machine}
    (test : run condition initial = .ok (post.push (.val (bword true))) 0) :
    run (emit condition left right) initial =
      (run left post).bind (fun next skip => exec ([.jump right.length] ++ right) skip next) := by
  unfold emit
  rw [run_append_ok test]
  rw [run_append_skip (m' := post) (k := 0) rfl]
  rw [exec_append]
  rfl

/-- Normally completing left code skips the entire right arm. The exact
returned machine retains every frame/world/stack fact supplied by G24. -/
theorem true_success {condition left right : List Instr} {initial post final : Machine}
    (test : run condition initial = .ok (post.push (.val (bword true))) 0)
    (body : run left post = .ok final 0) :
    run (emit condition left right) initial = .ok final 0 := by
  rw [true_run test, body]
  change exec right right.length final = .ok final 0
  exact exec_length right final

theorem true_revert {condition left right : List Instr} {initial post : Machine}
    (test : run condition initial = .ok (post.push (.val (bword true))) 0)
    (body : run left post = .revert) :
    run (emit condition left right) initial = .revert := by
  rw [true_run test, body]
  rfl

theorem true_fault {condition left right : List Instr} {initial post : Machine}
    (test : run condition initial = .ok (post.push (.val (bword true))) 0)
    (body : run left post = .fault) :
    run (emit condition left right) initial = .fault := by
  rw [true_run test, body]
  rfl

/-- A pending body jump is not an encoded source return: its first skipped
instruction is the emitter's jump-over-else. Keep the residual skip exact. -/
theorem true_pending_skip {condition left right : List Instr}
    {initial post final : Machine} {skip : Nat}
    (test : run condition initial = .ok (post.push (.val (bword true))) 0)
    (body : run left post = .ok final (skip + 1)) :
    run (emit condition left right) initial = exec right skip final := by
  rw [true_run test, body]
  rfl

theorem condition_revert {condition left right : List Instr} {initial : Machine}
    (test : run condition initial = .revert) :
    run (emit condition left right) initial = .revert := by
  unfold emit
  exact run_append_revert test

theorem condition_fault {condition left right : List Instr} {initial : Machine}
    (test : run condition initial = .fault) :
    run (emit condition left right) initial = .fault := by
  unfold emit run
  unfold run at test
  rw [exec_append, test]
  rfl
end Solidity.Backend.StructuredFlow.Branch
