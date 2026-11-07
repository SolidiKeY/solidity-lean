import tests.h62.item2.«audit-v09-passes».P20InterfaceV2Controls
import Solidity.Backend.Passes.CoreBoundary

/-! Regression: a projected core representation or suffix certificate must not
be counted as a jointly reached link without the actual successful prefix and
resource bound. This fixture witnesses the five public frozen CoreBoundary
premise bundles, retaining the actual output map. Its over-limit case is a
constructively inhabited negative premise bundle with refused Input, not a
successful-input witness. No heap ownership upgrade or full adequacy is claimed. -/
namespace Solidity.Backend.Passes.AuditCoreBoundary
open Evm Evm.Compiler
open Yul.Compilation.P20.InterfaceV2.Controls

def suffix : Solidity.Prog C Γ Γ := .nil

theorem suffix_certificate : inFragP compilation.frag suffix = some compilation.frag := by
  first | rfl | decide | omega | simp only []

theorem bound : (1 + Evm.Prog.pushes program) + Evm.Prog.pushes suffix ≤ Lmax := by
  first | decide | omega | rfl | simp only []

/-- Both link premises share the exact actual reached prefix and checked suffix. -/
theorem mapped_link :
    MappedBoundaryLink compilation (.core compilation.frag suffix_certificate)
      1 64 bases target machine :=
  compilation_core_mapped_link compilation suffix_certificate bound

theorem link :
    BoundaryLink compilation (.core compilation.frag suffix_certificate)
      1 64 bases bases target machine :=
  compilation_core_link compilation suffix_certificate bound

/-- The same successful source/target supplies both original Rep and mapped
output, so the two projection premise bundles are genuinely reached together. -/
theorem joint_reached : ∃ (out : Solidity.Out C target.H Γ)
    (final : Machine) (outBase : Nat → Fin W),
    compilation.Input 1 64 bases target machine ∧ Evm.Prog.pays program = false ∧
    program.run target = .ok out ∧ Evm.run compilation.code machine = .ok final 0 ∧
    compilation.Rep (1 + Evm.Prog.pushes program) 64 bases target machine out.st final ∧
    MappedOutput compilation (1 + Evm.Prog.pushes program) 64 bases target machine out.st final outBase ∧
    Sim C (1 + Evm.Prog.pushes program) 1 compilation.frag out.st final := by
  obtain ⟨out, final, source, _, ran, _, represented⟩ := complete_success
  obtain ⟨outBase, mapped⟩ := (mapped_output_iff compilation _ _ _ _ _ _ _).mp represented
  exact ⟨out, final, outBase, joint_input, rfl, source, ran, represented, mapped,
    mapped_output_core compilation mapped⟩

theorem rep_projection : ∃ (out : Solidity.Out C target.H Γ) (final : Machine),
    program.run target = .ok out ∧ Evm.run compilation.code machine = .ok final 0 ∧
    compilation.Rep (1 + Evm.Prog.pushes program) 64 bases target machine out.st final ∧
    Sim C (1 + Evm.Prog.pushes program) 1 compilation.frag out.st final := by
  obtain ⟨out, final, _, _, _, source, ran, represented, _, _⟩ := joint_reached
  exact ⟨out, final, source, ran, represented, compilation_rep_core compilation represented⟩

/-- Apply the universal link to its actual successful reached map. -/
theorem reached_suffix_input : ∃ (out : Solidity.Out C target.H Γ)
    (final : Machine) (outBase : Nat → Fin W),
    program.run target = .ok out ∧ Evm.run compilation.code machine = .ok final 0 ∧
    (Compilation.core (b := 1) compilation.frag suffix_certificate).Input
      (1 + Evm.Prog.pushes program) 64 outBase out.st final := by
  obtain ⟨out, final, outBase, _, _, source, ran, _, mapped, _⟩ := joint_reached
  exact ⟨out, final, outBase, source, ran, mapped_link out final outBase source ran mapped⟩

/-- The intentional negative theorem's hypotheses are simultaneously inhabited. -/
theorem resource_premises :
    inFragP compilation.frag suffix = some compilation.frag ∧
    Lmax < (Lmax + 1) + Evm.Prog.pushes suffix :=
  ⟨suffix_certificate, by decide⟩

theorem over_limit_refused :
    ¬ (Compilation.core (b := 1) compilation.frag suffix_certificate).Input
      (Lmax + 1) 64 bases target machine :=
  core_input_refused suffix_certificate resource_premises.2

/-- info: 'Solidity.Backend.Passes.AuditCoreBoundary.suffix_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCoreBoundary.suffix_certificate
/-- info: 'Solidity.Backend.Passes.AuditCoreBoundary.bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCoreBoundary.bound
/-- info: 'Solidity.Backend.Passes.AuditCoreBoundary.mapped_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCoreBoundary.mapped_link
/-- info: 'Solidity.Backend.Passes.AuditCoreBoundary.link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCoreBoundary.link
/-- info: 'Solidity.Backend.Passes.AuditCoreBoundary.joint_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCoreBoundary.joint_reached
/-- info: 'Solidity.Backend.Passes.AuditCoreBoundary.rep_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCoreBoundary.rep_projection
/-- info: 'Solidity.Backend.Passes.AuditCoreBoundary.reached_suffix_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCoreBoundary.reached_suffix_input
/-- info: 'Solidity.Backend.Passes.AuditCoreBoundary.resource_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCoreBoundary.resource_premises
/-- info: 'Solidity.Backend.Passes.AuditCoreBoundary.over_limit_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditCoreBoundary.over_limit_refused
end Solidity.Backend.Passes.AuditCoreBoundary
