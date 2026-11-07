import Solidity.Backend.Passes.MemoryCallScopeBoundary
import Solidity.Backend.Passes.MemoryCallFailures

namespace Solidity.Backend.Passes.MemoryCallScopeBoundary.Failures
open Evm Evm.Memory Evm.Compiler MemoryCallControls

/-- Only the actual successful allocation prefix is represented. No failed
output map, suffix Input or suffix execution is required. -/
theorem reached {P : Prog C Before MemoryCallFailures.Returned} {Ξ : Ctx}
    (bad : Calls.Program 1 allocation.frag P) (free : Evm.Prog.pushes P = 0)
    (payment : Evm.Prog.pays P = false) (failed : P.run first.st = .error .revert)
    (capacity : 1 + bad.need ≤ 128) (cost : bad.cost first.st ≤ 1)
    (Q : Prog C Before Ξ) (later : CompiledProg 1 (compiled bad).frag Q) :
    ((allocate.join (MemoryScopeBoundary.program P)).join Q).run initial = .error .revert ∧
    (allocate.join ((MemoryScopeBoundary.program P).join Q)).run initial = .error .revert ∧
    ∃ (selected : Nat → Fin W) (mid : Machine), mid.stack = [] ∧ ∀ tail,
      run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory allocation) 1 128 base initial {machine with stack := tail}
        first.st {mid with stack := tail} selected ∧
      (Compilation.memoryCalls (compiled bad) (scope_free free)).Input 1 128 selected first.st {mid with stack := tail} ∧
      run (compiled bad).code {mid with stack := tail} = .revert ∧
      run ((allocation.code ++ (compiled bad).code) ++ later.code) {machine with stack := tail} = .revert ∧
      run (allocation.code ++ ((compiled bad).code ++ later.code)) {machine with stack := tail} = .revert := by
  have scopeError := (MemoryScopeBoundary.source_error (P := P) .revert).mpr failed
  have suffixError : ((MemoryScopeBoundary.program P).join Q).run first.st = .error .revert := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq,scopeError]
  have joinedError : (allocate.join ((MemoryScopeBoundary.program P).join Q)).run initial = .error .revert := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq,first_source,suffixError,Except.map]
  refine ⟨by rw [typed_sequencing_assoc]; exact joinedError, joinedError, ?_⟩
  obtain ⟨selected,mid,empty,runs⟩ := MemoryCallFailures.reached bad free payment failed capacity cost
  refine ⟨selected,mid,empty,?_⟩
  intro tail
  obtain ⟨ha,ma,hi,hbad,_⟩ := runs tail
  have hs : run (compiled bad).code {mid with stack := tail} = .revert := by
    rw [code]
    exact hbad
  refine ⟨ha,ma,input bad free hi,hs,?_,?_⟩
  · have firstFailure : run (allocation.code ++ (compiled bad).code) {machine with stack := tail} = .revert :=
      (run_append_ok (c₂ := (compiled bad).code) ha).trans hs
    exact run_append_revert firstFailure
  · exact (run_append_ok (c₂ := (compiled bad).code ++ later.code) ha).trans (run_append_revert hs)

def unreachable : Prog C Before (.mem A :: Before) :=
  .cons (.declMem A (.user "unreachable") (some (.newArr (.lit 5 rfl) rfl)) rfl rfl) .nil
def later (F : Frag Before) : CompiledProg 1 F unreachable :=
  (Memory.compileProg 1 F unreachable).get (by rfl)

def argument_case := reached MemoryCallFailures.argument MemoryCallFailures.argument_free (by decide +kernel)
  MemoryCallFailures.argument_source MemoryCallFailures.frames.1
  (by rw [MemoryCallFailures.costs.1]; decide)
  unreachable (later (compiled MemoryCallFailures.argument).frag)

def body_case := reached MemoryCallFailures.body MemoryCallFailures.body_free (by decide +kernel)
  MemoryCallFailures.body_source MemoryCallFailures.frames.2
  (by rw [MemoryCallFailures.costs.2]; exact Nat.le_refl _)
  unreachable (later (compiled MemoryCallFailures.body).frag)

theorem distinct_costs : (compiled MemoryCallFailures.argument).cost first.st = 0 ∧
    (compiled MemoryCallFailures.body).cost first.st = 1 :=
  ⟨(cost MemoryCallFailures.argument first.st).trans MemoryCallFailures.costs.1,
    (cost MemoryCallFailures.body first.st).trans MemoryCallFailures.costs.2⟩

end Solidity.Backend.Passes.MemoryCallScopeBoundary.Failures
