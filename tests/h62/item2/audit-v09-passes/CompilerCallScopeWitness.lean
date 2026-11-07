import Solidity.Backend.Passes.CompilerCallScopeControls

/-! Guard accepting an empty public call-scope Input, skipping its consumer,
or corrupting the saved caller tail while preserving only a partial vector.
Reuse the actual public compiler result and its complete original observations. -/
namespace Solidity.Backend.Passes.AuditCompilerCallScope
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes
open MemoryCallControls

theorem joint :
    (Compilation.memory allocation).Input 1 128 base initial machine ∧
    Compiler.compile 1 allocation.frag MemoryCallScopeBoundary.Controls.scopeProgram =
      some CompilerCallScopeRecognition.actual ∧
    CompilerCallScopeRecognition.actual.isMemoryCalls = true ∧
    (∃ (mid : Machine) (selected : Nat → Fin W),
      MappedOutput (.memory allocation) 1 128 base initial machine first.st mid selected ∧
      CompilerCallScopeRecognition.actual.Input 1 128 selected first.st mid) := by
  refine ⟨MemoryCallControls.input, CompilerCallScopeRecognition.accepted,
    CompilerCallScopeRecognition.branch, ?_⟩
  obtain ⟨mid, hs, _, hr⟩ := compilation_success (.memory allocation)
    MemoryCallControls.input (by decide +kernel) first_source
  obtain ⟨selected, hm⟩ := (mapped_output_iff (.memory allocation) _ _ _ _ _ _ _).mp hr
  have mapped : MappedOutput (.memory allocation) 1 128 base initial machine first.st mid selected := by
    simpa only [MemoryCallApplication.allocation_free,Nat.add_zero] using hm
  exact ⟨mid, selected, mapped, CompilerCallScopeRecognition.into_actual first mid selected
    first_source hs mapped⟩
def prefix_vector := @Solidity.Backend.Passes.CompilerCallScopeRecognition.Controls.prefix_vector
def final_vector := @Solidity.Backend.Passes.CompilerCallScopeRecognition.Controls.final_vector
def skipped_consumer_refused := @Solidity.Backend.Passes.CompilerCallScopeRecognition.Controls.skipped_consumer_refused
def corrupted_tail_refused := @Solidity.Backend.Passes.CompilerCallScopeRecognition.Controls.corrupted_tail_refused

/-- info: 'Solidity.Backend.Passes.AuditCompilerCallScope.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCompilerCallScope.joint

/-- info: 'Solidity.Backend.Passes.AuditCompilerCallScope.prefix_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCompilerCallScope.prefix_vector

/-- info: 'Solidity.Backend.Passes.AuditCompilerCallScope.final_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCompilerCallScope.final_vector

/-- info: 'Solidity.Backend.Passes.AuditCompilerCallScope.skipped_consumer_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCompilerCallScope.skipped_consumer_refused

/-- info: 'Solidity.Backend.Passes.AuditCompilerCallScope.corrupted_tail_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCompilerCallScope.corrupted_tail_refused
end Solidity.Backend.Passes.AuditCompilerCallScope
