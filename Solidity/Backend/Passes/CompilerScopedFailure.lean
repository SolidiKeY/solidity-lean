import Solidity.Backend.Passes.MemoryCallScopeFailures

/-! Whole public recognition of the existing scoped argument/body failure
fixtures. These are internal coarse reverts; no post-failure map or ABI bytes
are supplied. The unreachable allocating suffix is retained in the program. -/
namespace Solidity.Backend.Passes.CompilerScopedFailure
open Evm Evm.Memory Evm.Compiler MemoryCallControls
open MemoryCallScopeBoundary

def argumentProgram : Prog C [] (.mem A :: Before) :=
  (allocate.join (MemoryScopeBoundary.program MemoryCallFailures.argumentProgram)).join Failures.unreachable

theorem argument_some : (Compiler.compile 1 (Frag.init []) argumentProgram).isSome = true := by
  decide +kernel
@[irreducible] def argumentActual : Compilation 1 (Frag.init []) argumentProgram :=
  (Compiler.compile 1 (Frag.init []) argumentProgram).get argument_some

theorem argument_accepted : Compiler.compile 1 (Frag.init []) argumentProgram = some argumentActual := by
  unfold argumentActual
  exact (Option.some_get _).symm

theorem argument_branch : argumentActual.isMemoryCalls = true := by with_unfolding_all decide +kernel
theorem argument_room : 1 + argumentActual.requiredFrame ≤ 128 := by with_unfolding_all decide +kernel
theorem argument_cost : argumentActual.allocationCost initial = 2 := by
  with_unfolding_all decide +kernel

theorem argument_input : argumentActual.Input 1 128 base initial machine := by
  apply (argumentActual.memoryCalls_input argument_branch 1 128 base initial machine).mpr
  refine ⟨initial_repr.1,argument_room,?_⟩
  rw [argument_cost]
  exact .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩

theorem argument_source : argumentProgram.run initial = .error .revert :=
  Failures.argument_case.1

theorem argument_target (tail : List Word) :
    run argumentActual.code {machine with stack := tail} = .revert :=
  (compilation_revert_iff argumentActual (compilation_input_stack argumentActual argument_input tail)
    (by decide +kernel)).mpr (.inl argument_source)

theorem argument_not_panic : argumentProgram.run initial ≠ .error .panic := by
  rw [argument_source]
  intro h
  cases Except.error.inj h

theorem argument_not_diverge : argumentProgram.run initial ≠ .error .diverge := by
  rw [argument_source]
  intro h
  cases Except.error.inj h

def bodyProgram : Prog C [] (.mem A :: Before) :=
  (allocate.join (MemoryScopeBoundary.program MemoryCallFailures.bodyProgram)).join Failures.unreachable

theorem body_some : (Compiler.compile 1 (Frag.init []) bodyProgram).isSome = true := by
  decide +kernel
@[irreducible] def bodyActual : Compilation 1 (Frag.init []) bodyProgram :=
  (Compiler.compile 1 (Frag.init []) bodyProgram).get body_some

theorem body_accepted : Compiler.compile 1 (Frag.init []) bodyProgram = some bodyActual := by
  unfold bodyActual
  exact (Option.some_get _).symm

theorem body_branch : bodyActual.isMemoryCalls = true := by with_unfolding_all decide +kernel
theorem body_room : 1 + bodyActual.requiredFrame ≤ 128 := by with_unfolding_all decide +kernel
theorem body_cost : bodyActual.allocationCost initial = 3 := by
  with_unfolding_all decide +kernel

theorem body_input : bodyActual.Input 1 128 base initial machine := by
  apply (bodyActual.memoryCalls_input body_branch 1 128 base initial machine).mpr
  refine ⟨initial_repr.1,body_room,?_⟩
  rw [body_cost]
  exact .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩

theorem body_source : bodyProgram.run initial = .error .revert :=
  Failures.body_case.1

theorem body_target (tail : List Word) :
    run bodyActual.code {machine with stack := tail} = .revert :=
  (compilation_revert_iff bodyActual (compilation_input_stack bodyActual body_input tail)
    (by decide +kernel)).mpr (.inl body_source)

theorem body_not_panic : bodyProgram.run initial ≠ .error .panic := by
  rw [body_source]
  intro h
  cases Except.error.inj h

theorem body_not_diverge : bodyProgram.run initial ≠ .error .diverge := by
  rw [body_source]
  intro h
  cases Except.error.inj h

/-- Both calls are reached after allocation, but argument failure prevents the
return-default allocation which the failing body reaches. The unreachable
five-element suffix contributes no reached cost in either case. -/
theorem reached_costs_differ : argumentActual.allocationCost initial + 1 =
    bodyActual.allocationCost initial := by
  rw [argument_cost,body_cost]

theorem target_not_fault (tail : List Word) :
    run argumentActual.code {machine with stack := tail} ≠ .fault ∧
    run bodyActual.code {machine with stack := tail} ≠ .fault := by
  rw [argument_target,body_target]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_self]

end Solidity.Backend.Passes.CompilerScopedFailure
