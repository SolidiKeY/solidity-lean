import Solidity.Backend.Passes.ReframedControls

/-! Guard silently replacing the call prefix's 128-slot frame by its consuming
suffix's 5-slot frame, losing full saved-tail observations, or fabricating a
post-failure map when a reached suffix reverts. Reuse the existing shrinking link. -/
namespace Solidity.Backend.Passes.AuditReframed
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes

theorem joint :
    ReframedControls.left.Input 1 128 MemoryCallControls.base
      MemoryCallControls.initial MemoryCallControls.machine ∧
    MemoryCallReuse.prefixProgram.run MemoryCallControls.initial = .ok MemoryCallReuse.before ∧
    MemoryCallControls.consume.run MemoryCallReuse.before.st = .ok MemoryCallControls.final ∧
    5 < 1 + MemoryCallReuse.leading.need ∧
    1 + MemoryCallControls.After.length ≤ 5 ∧
    1 + frameNeedProg MemoryCallControls.consume ≤ 5 ∧
    ReframedControls.badProg.run MemoryCallReuse.before.st = .error .revert :=
  ⟨MemoryCallReuseApplication.input,MemoryCallReuse.prefix_source,MemoryCallControls.final_source,
    ReframedControls.frame_gap.1,ReframedControls.frame_gap.2.1,
    ReframedControls.frame_gap.2.2,ReframedControls.bad_source⟩
def frame_gap := @Solidity.Backend.Passes.ReframedControls.frame_gap
def prefix_refused_at_suffix_frame := @Solidity.Backend.Passes.ReframedControls.prefix_refused_at_suffix_frame
def physical_link := @Solidity.Backend.Passes.ReframedControls.physical_link
def shared := @Solidity.Backend.Passes.ReframedControls.shared
def bad_source := @Solidity.Backend.Passes.ReframedControls.bad_source
def bad_link := @Solidity.Backend.Passes.ReframedControls.bad_link
def reached_revert := @Solidity.Backend.Passes.ReframedControls.reached_revert
def ordered_vectors := @Solidity.Backend.Passes.ReframedControls.ordered_vectors
def skipped_consumer := @Solidity.Backend.Passes.ReframedControls.skipped_consumer
def corrupted_tail := @Solidity.Backend.Passes.ReframedControls.corrupted_tail
def short_suffix_frame := @Solidity.Backend.Passes.ReframedControls.short_suffix_frame

/-- info: 'Solidity.Backend.Passes.AuditReframed.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.joint

/-- info: 'Solidity.Backend.Passes.AuditReframed.frame_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.frame_gap

/-- info: 'Solidity.Backend.Passes.AuditReframed.prefix_refused_at_suffix_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.prefix_refused_at_suffix_frame

/-- info: 'Solidity.Backend.Passes.AuditReframed.physical_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.physical_link

/-- info: 'Solidity.Backend.Passes.AuditReframed.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.shared

/-- info: 'Solidity.Backend.Passes.AuditReframed.bad_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.bad_source

/-- info: 'Solidity.Backend.Passes.AuditReframed.bad_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.bad_link

/-- info: 'Solidity.Backend.Passes.AuditReframed.reached_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.reached_revert

/-- info: 'Solidity.Backend.Passes.AuditReframed.ordered_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.ordered_vectors

/-- info: 'Solidity.Backend.Passes.AuditReframed.skipped_consumer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.skipped_consumer

/-- info: 'Solidity.Backend.Passes.AuditReframed.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.corrupted_tail

/-- info: 'Solidity.Backend.Passes.AuditReframed.short_suffix_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditReframed.short_suffix_frame
end Solidity.Backend.Passes.AuditReframed
