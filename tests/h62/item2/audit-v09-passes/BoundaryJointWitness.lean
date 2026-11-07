import tests.h62.item2.«audit-v09-passes».P20InterfaceV2Controls

/-! Regression: separate inhabitation of compiler premises must not be counted
as a joint witness. This fixture supplies the same checked compilation, source
state, actual machine, no-payment proof, successful source output and successful
target for the four unchanged public Boundary theorems. A separately checked
reverting program guards source/target failure transport and rejects a forged
success result on the same populated input. A shared false-guard family retains
the require/revert versus assert/panic source distinction despite equal coarse
target observations. It guards against
reject-all/always-revert and always-fault outcomes on that supported input.
Only these four frozen theorem premise bundles are witnessed here; no claim
covers the remaining audit declarations or concrete gas/fork adequacy. -/
namespace Solidity.Backend.Passes.AuditBoundary
open Evm Evm.Compiler
open Yul.Compilation.P20.InterfaceV2.Controls

/-- All explicit hypotheses of compilation_exact, compilation_success,
compilation_reflect_success and compilation_revert_iff hold together. -/
theorem joint : ∃ (out : Solidity.Out C target.H Γ) (final : Machine),
    compilation.Input 1 64 bases target machine ∧
    Evm.Prog.pays program = false ∧
    program.run target = .ok out ∧
    Evm.run compilation.code machine = .ok final 0 ∧
    final.stack = machine.stack ∧
    compilation.Rep (1 + Evm.Prog.pushes program) 64 bases target machine out.st final := by
  obtain ⟨out, final, source, _, ran, stack, represented⟩ := complete_success
  exact ⟨out, final, joint_input, rfl, source, ran, stack, represented⟩

/-- General successful-execution discrimination, independent of the fixture. -/
theorem success_excludes_rejection (code : List Evm.Instr) (initial final : Machine)
    (ran : Evm.run code initial = .ok final 0) :
    Evm.run code initial ≠ .revert ∧ Evm.run code initial ≠ .fault := by
  constructor <;> intro rejected <;> rw [ran] at rejected <;> cases rejected

/-- Both trivial target outcomes violate the supported joint-success witness. -/
theorem supported_not_trivial :
    Evm.run compilation.code machine ≠ .revert ∧
    Evm.run compilation.code machine ≠ .fault := by
  obtain ⟨_, final, _, _, _, ran, _, _⟩ := joint
  exact success_excludes_rejection compilation.code machine final ran

/-- info: 'Solidity.Backend.Passes.AuditBoundary.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.joint
/-- info: 'Solidity.Backend.Passes.AuditBoundary.success_excludes_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.success_excludes_rejection
/-- info: 'Solidity.Backend.Passes.AuditBoundary.supported_not_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.supported_not_trivial
namespace Reverting

def program : Solidity.Prog C Γ Γ := .cons .revert .nil

def compilation : Evm.Compiler.Compilation 1 F program :=
  .core F (by first | rfl | decide | omega | simp only [])

theorem selected : Evm.Compiler.compile 1 F program = some compilation := by
  first | rfl | decide | omega | simp only []

theorem input : compilation.Input 1 64 bases target machine := by
  exact ⟨Backend.Passes.AssignmentSubtractionPass.Controls.initial.core, by decide⟩

theorem source_run : program.run target = .error .revert := by
  first | rfl | decide | omega | simp only []

theorem target_run : Evm.run compilation.code machine = .revert := by
  first | rfl | decide | omega | simp only []

/-- Actual admission and source/target failure hold on the same populated input. -/
theorem joint_failure : compilation.Input 1 64 bases target machine ∧
    Evm.Prog.pays program = false ∧ program.run target = .error .revert ∧
    Evm.run compilation.code machine = .revert :=
  ⟨input, rfl, source_run, target_run⟩

/-- Instantiate the unchanged public transport on an actual reverting source. -/
theorem transported_failure : Evm.run compilation.code machine = .revert :=
  (compilation_revert_iff compilation input rfl).mpr (.inl source_run)

/-- A forged successful target cannot satisfy the actual failure observation. -/
theorem success_refused (final : Machine) :
    Evm.run compilation.code machine ≠ .ok final 0 := by
  intro fake
  have incompatible := target_run.symm.trans fake
  cases incompatible

/-- info: 'Solidity.Backend.Passes.AuditBoundary.Reverting.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.Reverting.selected
/-- info: 'Solidity.Backend.Passes.AuditBoundary.Reverting.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.Reverting.input
/-- info: 'Solidity.Backend.Passes.AuditBoundary.Reverting.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.Reverting.source_run
/-- info: 'Solidity.Backend.Passes.AuditBoundary.Reverting.target_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.Reverting.target_run
/-- info: 'Solidity.Backend.Passes.AuditBoundary.Reverting.joint_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.Reverting.joint_failure
/-- info: 'Solidity.Backend.Passes.AuditBoundary.Reverting.transported_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.Reverting.transported_failure
/-- info: 'Solidity.Backend.Passes.AuditBoundary.Reverting.success_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.Reverting.success_refused
end Reverting
namespace GuardFailure

/-- A shared false guard retains the actual assert/require source distinction. -/
def program (asserting : Bool) : Solidity.Prog C Γ Γ :=
  .cons (if asserting then .assert (.simple (.bool false))
    else .require (.simple (.bool false))) .nil

def compilation (asserting : Bool) : Evm.Compiler.Compilation 1 F (program asserting) :=
  .core F (by cases asserting <;> first | rfl | decide | omega | simp only [])

theorem selected (asserting : Bool) :
    Evm.Compiler.compile 1 F (program asserting) = some (compilation asserting) := by
  cases asserting <;> first | rfl | decide | omega | simp only []

theorem input (asserting : Bool) :
    (compilation asserting).Input 1 64 bases target machine := by
  exact ⟨Backend.Passes.AssignmentSubtractionPass.Controls.initial.core,
    by cases asserting <;> decide⟩

theorem source_run (asserting : Bool) :
    (program asserting).run target = .error (if asserting then .panic else .revert) := by
  cases asserting <;> first | rfl | decide | omega | simp only []

theorem target_run (asserting : Bool) :
    Evm.run (compilation asserting).code machine = .revert := by
  cases asserting <;> first | rfl | decide | omega | simp only []

/-- The panic alternative retains the original actual asserts guard. -/
theorem source_alternative (asserting : Bool) :
    (program asserting).run target = .error .revert ∨
    ((program asserting).asserts = true ∧ (program asserting).run target = .error .panic) := by
  cases asserting
  · exact .inl (source_run false)
  · exact .inr ⟨rfl, source_run true⟩

theorem joint_failure (asserting : Bool) :
    (compilation asserting).Input 1 64 bases target machine ∧
    Evm.Prog.pays (program asserting) = false ∧
    ((program asserting).run target = .error .revert ∨
      ((program asserting).asserts = true ∧ (program asserting).run target = .error .panic)) ∧
    Evm.run (compilation asserting).code machine = .revert :=
  ⟨input asserting, by cases asserting <;> rfl, source_alternative asserting, target_run asserting⟩

theorem transported_failure (asserting : Bool) :
    Evm.run (compilation asserting).code machine = .revert :=
  (compilation_revert_iff (compilation asserting) (input asserting)
    (by cases asserting <;> rfl)).mpr (source_alternative asserting)

/-- Coarse target equality must not be misreported as equal source failures. -/
theorem source_distinct : (program true).run target ≠ (program false).run target := by
  intro same
  rw [source_run, source_run] at same
  cases same

theorem coarse_target_equal : Evm.run (compilation true).code machine =
    Evm.run (compilation false).code machine :=
  (target_run true).trans (target_run false).symm

/-- info: 'Solidity.Backend.Passes.AuditBoundary.GuardFailure.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.GuardFailure.selected
/-- info: 'Solidity.Backend.Passes.AuditBoundary.GuardFailure.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.GuardFailure.input
/-- info: 'Solidity.Backend.Passes.AuditBoundary.GuardFailure.source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.GuardFailure.source_run
/-- info: 'Solidity.Backend.Passes.AuditBoundary.GuardFailure.target_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.GuardFailure.target_run
/-- info: 'Solidity.Backend.Passes.AuditBoundary.GuardFailure.source_alternative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.GuardFailure.source_alternative
/-- info: 'Solidity.Backend.Passes.AuditBoundary.GuardFailure.joint_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.GuardFailure.joint_failure
/-- info: 'Solidity.Backend.Passes.AuditBoundary.GuardFailure.transported_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.GuardFailure.transported_failure
/-- info: 'Solidity.Backend.Passes.AuditBoundary.GuardFailure.source_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.GuardFailure.source_distinct
/-- info: 'Solidity.Backend.Passes.AuditBoundary.GuardFailure.coarse_target_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditBoundary.GuardFailure.coarse_target_equal
end GuardFailure
end Solidity.Backend.Passes.AuditBoundary
