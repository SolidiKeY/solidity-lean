import Solidity.Backend.Passes.LoopCallControls
import Solidity.Backend.Passes.LoopScopeTerminal

/-! Guard vacuous post-loop call admission, stale alias substitution and using
an unexpanded caller frame. Reuse the actual loop-selected maps; staged success
remains distinct from the original whole-mixture recognizer refusal. -/
namespace Solidity.Backend.Passes.AuditLoopCall
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes

theorem joint :
    (Compilation.memory LoopScopeControls.preparation).Input 1 128 MemoryCallControls.base
      MemoryCallControls.initial MemoryCallControls.machine ∧
    LoopCallControls.call.run LoopScopeControls.loopOut.st = .ok LoopCallControls.result ∧
    (∃ mb nb,
      MappedOutput (.memory LoopScopeControls.preparation) 1 128 MemoryCallControls.base
        MemoryCallControls.initial MemoryCallControls.machine LoopScopeControls.prepared.st
        LoopScopeTrace.preparedTarget mb ∧
      MappedOutput LoopScopeControls.checked 1 128 mb LoopScopeControls.prepared.st
        LoopScopeTrace.preparedTarget LoopScopeControls.loopOut.st LoopScopeTrace.loopTarget nb ∧
      LoopCallControls.checkedCall.Input 1 128 nb LoopScopeControls.loopOut.st LoopScopeTrace.loopTarget) := by
  refine ⟨LoopScopeApplication.preparation_input, LoopCallControls.source, ?_⟩
  obtain ⟨mb, nb, ha, hb⟩ := LoopScopeTerminal.prefix_relations
  exact ⟨mb, nb, ha, hb, LoopCallControls.receiving ha hb⟩
def free := @Solidity.Backend.Passes.LoopCallControls.free
def source := @Solidity.Backend.Passes.LoopCallControls.source
def cost := @Solidity.Backend.Passes.LoopCallControls.cost
def expanded_frame := @Solidity.Backend.Passes.LoopCallControls.expanded_frame
def public_recognizer := @Solidity.Backend.Passes.LoopCallControls.public_recognizer
def whole_recognizer_refused := @Solidity.Backend.Passes.LoopCallControls.whole_recognizer_refused
def joined_source := @Solidity.Backend.Passes.LoopCallControls.joined_source
def receiving := @Solidity.Backend.Passes.LoopCallControls.receiving
def private_frame_refused := @Solidity.Backend.Passes.LoopCallControls.private_frame_refused

/-- info: 'Solidity.Backend.Passes.AuditLoopCall.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopCall.joint

/-- info: 'Solidity.Backend.Passes.AuditLoopCall.free' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopCall.free

/-- info: 'Solidity.Backend.Passes.AuditLoopCall.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopCall.source

/-- info: 'Solidity.Backend.Passes.AuditLoopCall.cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopCall.cost

/-- info: 'Solidity.Backend.Passes.AuditLoopCall.expanded_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopCall.expanded_frame

/-- info: 'Solidity.Backend.Passes.AuditLoopCall.public_recognizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopCall.public_recognizer

/-- info: 'Solidity.Backend.Passes.AuditLoopCall.whole_recognizer_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopCall.whole_recognizer_refused

/-- info: 'Solidity.Backend.Passes.AuditLoopCall.joined_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopCall.joined_source

/-- info: 'Solidity.Backend.Passes.AuditLoopCall.receiving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopCall.receiving

/-- info: 'Solidity.Backend.Passes.AuditLoopCall.private_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopCall.private_frame_refused
end Solidity.Backend.Passes.AuditLoopCall
