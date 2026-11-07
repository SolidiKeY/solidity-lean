import Solidity.Backend.Passes.LoopPrefixControls

/-! Guard empty loop-prefix admission, erased effects before a reached revert,
and confusing source divergence with revert or panic. The original finite-prefix
and nontermination proofs are reused; no infinite evaluator or native gas claim. -/
namespace Solidity.Backend.Passes.AuditLoopPrefix
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes

theorem joint :
    (Compilation.memory LoopScopeControls.preparation).Input 1 128 MemoryCallControls.base
      MemoryCallControls.initial MemoryCallControls.machine ∧
    LoopPrefixControls.failureScope.run LoopScopeControls.prepared.st = .error .revert ∧
    LoopPrefixControls.spinScope.run LoopScopeControls.loopOut.st = .error .diverge ∧
    (∃ selected, (Compilation.memoryLoopScopes LoopPrefixControls.failureCompiled).Input
      1 128 selected LoopScopeControls.prepared.st {LoopScopeTrace.preparedTarget with stack := []}) ∧
    (∃ selected, (Compilation.memoryLoopScopes LoopPrefixControls.spinCompiled).Input
      1 128 selected LoopScopeControls.loopOut.st {LoopScopeTrace.loopTarget with stack := []}) := by
  refine ⟨LoopScopeApplication.preparation_input, LoopPrefixControls.scope_failure,
    LoopPrefixControls.spin_scope_source, ?_, ?_⟩
  · obtain ⟨mb, all⟩ := LoopPrefixControls.reached_body_failure
    exact ⟨mb, (all []).2.1⟩
  · obtain ⟨mb, nb, all⟩ := LoopPrefixControls.reached_divergence
    exact ⟨nb, (all []).2.2.1⟩
def body_failure := @Solidity.Backend.Passes.LoopPrefixControls.body_failure
def failed_cost := @Solidity.Backend.Passes.LoopPrefixControls.failed_cost
def loop_failure := @Solidity.Backend.Passes.LoopPrefixControls.loop_failure
def scope_failure := @Solidity.Backend.Passes.LoopPrefixControls.scope_failure
def failed_room := @Solidity.Backend.Passes.LoopPrefixControls.failed_room
def reached_body_failure := @Solidity.Backend.Passes.LoopPrefixControls.reached_body_failure
def effect_target := @Solidity.Backend.Passes.LoopPrefixControls.effect_target
def emitted_failure := @Solidity.Backend.Passes.LoopPrefixControls.emitted_failure
def failing_body_target := @Solidity.Backend.Passes.LoopPrefixControls.failing_body_target
def condition_target := @Solidity.Backend.Passes.LoopPrefixControls.condition_target
def actual_failing_turn := @Solidity.Backend.Passes.LoopPrefixControls.actual_failing_turn
def failing_prefix_vector := @Solidity.Backend.Passes.LoopPrefixControls.failing_prefix_vector
def skipped_failure_effect := @Solidity.Backend.Passes.LoopPrefixControls.skipped_failure_effect
def spin_condition := @Solidity.Backend.Passes.LoopPrefixControls.spin_condition
def spin_source := @Solidity.Backend.Passes.LoopPrefixControls.spin_source
def spin_scope_source := @Solidity.Backend.Passes.LoopPrefixControls.spin_scope_source
def reached_divergence := @Solidity.Backend.Passes.LoopPrefixControls.reached_divergence
def distinct_failures := @Solidity.Backend.Passes.LoopPrefixControls.distinct_failures

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.joint

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.body_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.body_failure

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.failed_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.failed_cost

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.loop_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.loop_failure

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.scope_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.scope_failure

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.failed_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.failed_room

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.reached_body_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.reached_body_failure

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.effect_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.effect_target

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.emitted_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.emitted_failure

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.failing_body_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.failing_body_target

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.condition_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.condition_target

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.actual_failing_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.actual_failing_turn

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.failing_prefix_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.failing_prefix_vector

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.skipped_failure_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.skipped_failure_effect

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.spin_condition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.spin_condition

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.spin_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.spin_source

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.spin_scope_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.spin_scope_source

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.reached_divergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.reached_divergence

/-- info: 'Solidity.Backend.Passes.AuditLoopPrefix.distinct_failures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopPrefix.distinct_failures
end Solidity.Backend.Passes.AuditLoopPrefix
