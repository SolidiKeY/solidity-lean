import tests.h62.item2.«audit-v09-passes».P20InterfaceV2Controls
import Solidity.Backend.Passes.CoreBoundary
import Solidity.Backend.Passes.Sequence

/-! Regression: independently inhabited stage certificates must not be counted
as a reached sequencing witness. The same actual store and checked empty suffix
jointly supply Input, source success, payment freedom and the correlated suffix
link for the four public frozen Sequence declarations. Both original Rep
observations remain visible. This core/empty-suffix instance does not establish
other compiler branches, resource adequacy or whole-audit completion. -/
namespace Solidity.Backend.Passes.AuditSequence
open Evm Evm.Compiler
open Yul.Compilation.P20.InterfaceV2.Controls

def suffix : Solidity.Prog C Γ Γ := .nil

def suffixOutput (σ : State C Γ) : Solidity.Out C σ.H Γ :=
  ⟨σ, List.prefix_refl _⟩

theorem suffix_certificate : inFragP compilation.frag suffix = some compilation.frag := by
  first | rfl | decide | omega | simp only []

def suffixCompilation : Compilation 1 compilation.frag suffix :=
  .core compilation.frag suffix_certificate

theorem link : BoundaryLink compilation suffixCompilation 1 64 bases bases target machine :=
  compilation_core_link compilation suffix_certificate (by decide)

theorem source_suffix : suffix.run (output target).st = .ok (suffixOutput (output target).st) := by
  first | rfl | decide | omega | simp only []

/-- All common stage hypotheses hold together, not on unrelated inputs. -/
theorem premises : compilation.Input 1 64 bases target machine ∧
    BoundaryLink compilation suffixCompilation 1 64 bases bases target machine ∧
    Evm.Prog.pays program = false ∧ Evm.Prog.pays suffix = false ∧
    program.run target = .ok (output target) ∧
    suffix.run (output target).st = .ok (suffixOutput (output target).st) :=
  ⟨joint_input, link, rfl, rfl, source_run target, source_suffix⟩

theorem successful_sequence : ∃ mid final : Machine,
    (program.join suffix).run target = .ok
      ⟨(suffixOutput (output target).st).st,
        (output target).ext.trans (suffixOutput (output target).st).ext⟩ ∧
    Evm.run compilation.code machine = .ok mid 0 ∧
    Evm.run (compilation.code ++ suffixCompilation.code) machine = .ok final 0 ∧
    final.stack = machine.stack ∧
    compilation.Rep (1 + Evm.Prog.pushes program) 64 bases target machine (output target).st mid ∧
    suffixCompilation.Rep ((1 + Evm.Prog.pushes program) + Evm.Prog.pushes suffix)
      64 bases (output target).st mid (suffixOutput (output target).st).st final :=
  compilation_sequence_success compilation suffixCompilation premises.1 premises.2.1
    premises.2.2.1 premises.2.2.2.1 premises.2.2.2.2.1 premises.2.2.2.2.2

theorem failure_boundary : Evm.run (compilation.code ++ suffixCompilation.code) machine = .revert ↔
    TerminalFailure program target ∨ ∃ out, program.run target = .ok out ∧ TerminalFailure suffix out.st :=
  compilation_sequence_revert_iff compilation suffixCompilation premises.1 premises.2.1
    premises.2.2.1 premises.2.2.2.1

/-- The supported joined execution cannot be replaced by a trivial rejection. -/
theorem not_rejected : Evm.run (compilation.code ++ suffixCompilation.code) machine ≠ .revert := by
  obtain ⟨_, _, _, _, ran, _, _, _⟩ := successful_sequence
  intro rejected
  have incompatible := ran.symm.trans rejected
  cases incompatible

theorem typed_association : (program.join suffix).join suffix = program.join (suffix.join suffix) :=
  typed_sequencing_assoc program suffix suffix

theorem associations :
    ((program.join suffix).join suffix).run target = (program.join (suffix.join suffix)).run target ∧
    Evm.run ((compilation.code ++ suffixCompilation.code) ++ suffixCompilation.code) machine =
      Evm.run (compilation.code ++ (suffixCompilation.code ++ suffixCompilation.code)) machine :=
  compilation_sequence_associative compilation suffixCompilation suffixCompilation target machine

/-- info: 'Solidity.Backend.Passes.AuditSequence.suffix_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSequence.suffix_certificate
/-- info: 'Solidity.Backend.Passes.AuditSequence.link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSequence.link
/-- info: 'Solidity.Backend.Passes.AuditSequence.source_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSequence.source_suffix
/-- info: 'Solidity.Backend.Passes.AuditSequence.premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSequence.premises
/-- info: 'Solidity.Backend.Passes.AuditSequence.successful_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSequence.successful_sequence
/-- info: 'Solidity.Backend.Passes.AuditSequence.failure_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSequence.failure_boundary
/-- info: 'Solidity.Backend.Passes.AuditSequence.not_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSequence.not_rejected
/-- info: 'Solidity.Backend.Passes.AuditSequence.typed_association' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSequence.typed_association
/-- info: 'Solidity.Backend.Passes.AuditSequence.associations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSequence.associations
end Solidity.Backend.Passes.AuditSequence
