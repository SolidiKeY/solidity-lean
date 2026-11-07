import Solidity.Backend.Passes.LoopReframedFailureControls

/-! Guard stale alias admission after a loop, swapping a failing suffix before
the loop, and conflating ordinary revert with panic/divergence. Reuse exact
loop-selected maps and the original shrinking link; no native gas/ABI claim. -/
namespace Solidity.Backend.Passes.AuditLoopReframedFailure
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes

theorem joint :
    (Compilation.memory LoopScopeControls.preparation).Input 1 128 MemoryCallControls.base
      MemoryCallControls.initial MemoryCallControls.machine ∧
    LoopReframedFailureControls.demandOld.run LoopScopeControls.prepared.st =
      .ok ⟨LoopScopeControls.prepared.st,List.prefix_refl _⟩ ∧
    LoopReframedFailureControls.demandOld.run LoopScopeControls.loopOut.st = .error .revert ∧
    (∃ mb nb,
      MappedOutput (.memory LoopScopeControls.preparation) 1 128 MemoryCallControls.base
        MemoryCallControls.initial MemoryCallControls.machine LoopScopeControls.prepared.st
        LoopScopeTrace.preparedTarget mb ∧
      MappedOutput LoopScopeControls.checked 1 128 mb LoopScopeControls.prepared.st
        LoopScopeTrace.preparedTarget LoopScopeControls.loopOut.st LoopScopeTrace.loopTarget nb ∧
      (Compilation.memory LoopReframedFailureControls.afterCheck).Input 1 5 nb
        LoopScopeControls.loopOut.st LoopScopeTrace.loopTarget) := by
  refine ⟨LoopScopeApplication.preparation_input, LoopReframedFailureControls.before_source,
    LoopReframedFailureControls.after_source, ?_⟩
  obtain ⟨mb, nb, ha, hb⟩ := LoopScopeTerminal.prefix_relations
  refine ⟨mb, nb, ha, hb, ?_⟩
  have step := LoopReframedFailureControls.after_link
    (selected := mb) (mid := LoopScopeTrace.preparedTarget)
    LoopScopeControls.loopOut LoopScopeTrace.loopTarget nb LoopScopeControls.wrapped_source
    LoopScopeTrace.loop_target
    (by simpa only [LoopScopeControls.enclosed.cert.pushes_zero,Nat.add_zero] using hb)
  simpa only [LoopScopeControls.enclosed.cert.pushes_zero,Nat.add_zero] using step
def before_source := @Solidity.Backend.Passes.LoopReframedFailureControls.before_source
def after_source := @Solidity.Backend.Passes.LoopReframedFailureControls.after_source
def after_link := @Solidity.Backend.Passes.LoopReframedFailureControls.after_link
def reached_prefix_failure := @Solidity.Backend.Passes.LoopReframedFailureControls.reached_prefix_failure
def joined_source_failure := @Solidity.Backend.Passes.LoopReframedFailureControls.joined_source_failure
def before_target := @Solidity.Backend.Passes.LoopReframedFailureControls.before_target
def before_target_tail := @Solidity.Backend.Passes.LoopReframedFailureControls.before_target_tail
def wrong_order_target := @Solidity.Backend.Passes.LoopReframedFailureControls.wrong_order_target
def wrong_order_source := @Solidity.Backend.Passes.LoopReframedFailureControls.wrong_order_source
def wrong_order_distinct := @Solidity.Backend.Passes.LoopReframedFailureControls.wrong_order_distinct
def complete_wrong_order_vector := @Solidity.Backend.Passes.LoopReframedFailureControls.complete_wrong_order_vector
def corrupt_saved_tail := @Solidity.Backend.Passes.LoopReframedFailureControls.corrupt_saved_tail
def insufficient_guard_frame := @Solidity.Backend.Passes.LoopReframedFailureControls.insufficient_guard_frame
def stale_guard_input_refused := @Solidity.Backend.Passes.LoopReframedFailureControls.stale_guard_input_refused
def ordinary_revert_separate := @Solidity.Backend.Passes.LoopReframedFailureControls.ordinary_revert_separate

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.joint

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.before_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.before_source

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.after_source

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.after_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.after_link

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.reached_prefix_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.reached_prefix_failure

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.joined_source_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.joined_source_failure

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.before_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.before_target

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.before_target_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.before_target_tail

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.wrong_order_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.wrong_order_target

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.wrong_order_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.wrong_order_source

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.wrong_order_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.wrong_order_distinct

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.complete_wrong_order_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.complete_wrong_order_vector

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.corrupt_saved_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.corrupt_saved_tail

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.insufficient_guard_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.insufficient_guard_frame

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.stale_guard_input_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.stale_guard_input_refused

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.ordinary_revert_separate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.ordinary_revert_separate

macro "loopReframedPrivate%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.LoopReframedFailureControls 0) ++
    `Solidity.Backend.Passes.LoopReframedFailureControls ++ n.getId))

def guard_code : LoopReframedFailureControls.beforeCheck.code =
    (loopReframedPrivate% beforeValue).code ++ assertTop :=
  loopReframedPrivate% guard_code

def before_value : LoopReframedFailureControls.oldValue.evalT LoopScopeControls.prepared.st =
    .ok true := loopReframedPrivate% before_value

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.guard_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.guard_code
/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.before_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.before_value
/-- info: _private.Solidity.Backend.Passes.LoopReframedFailureControls.0.Solidity.Backend.Passes.LoopReframedFailureControls.guard_code: [propext,
 Quot.sound,
 Classical.choice]
---
info: _private.Solidity.Backend.Passes.LoopReframedFailureControls.0.Solidity.Backend.Passes.LoopReframedFailureControls.before_value: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
run_cmd do
  for short in [`guard_code, `before_value] do
    let name := (Lean.Name.num `_private.Solidity.Backend.Passes.LoopReframedFailureControls 0) ++
      `Solidity.Backend.Passes.LoopReframedFailureControls ++ short
    let axes ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axes}"

-- Exact original private refutation; never register its premises as inhabited.
example {target : Machine}
    (pointers : PointerRepr LoopScopeControls.loopOut.st LoopScopeTrace.oldOnly 1 target)
    (observed : (match target.mem 3 with
      | .val value => some value.val | _ => none) = some 258) : False :=
  (loopReframedPrivate% stale_pointer) pointers observed

theorem stale_pointer_premises_impossible (target : Machine) :
    ¬ (PointerRepr LoopScopeControls.loopOut.st LoopScopeTrace.oldOnly 1 target ∧
      (match target.mem 3 with
      | .val value => some value.val | _ => none) = some 258) := by
  rintro ⟨pointers, observed⟩
  exact (loopReframedPrivate% stale_pointer) pointers observed

/-- info: 'Solidity.Backend.Passes.AuditLoopReframedFailure.stale_pointer_premises_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopReframedFailure.stale_pointer_premises_impossible
/-- info: _private.Solidity.Backend.Passes.LoopReframedFailureControls.0.Solidity.Backend.Passes.LoopReframedFailureControls.stale_pointer: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
run_cmd do
  let name := (Lean.Name.num `_private.Solidity.Backend.Passes.LoopReframedFailureControls 0) ++
    `Solidity.Backend.Passes.LoopReframedFailureControls.stale_pointer
  let axes ← Lean.collectAxioms name
  Lean.logInfo m!"{name}: {axes}"
end Solidity.Backend.Passes.AuditLoopReframedFailure
