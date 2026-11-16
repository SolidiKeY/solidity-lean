import Solidity.Assurance.NonVacuityH28.Families
import Solidity.Backend.Payments.Headlines
import Solidity.Backend.Payments.EntrySuccess

/-!
# Inhabited applications of the H98 versioned compiler headlines

Guards V2 migration losing actual headline applications, and a reject-all or
always-revert checked entry satisfying only conditional agreement. Reuses the
existing nonempty require family, jointly constructed simulation and source run;
no per-case program copies, new premises or changed frozen witnesses.
-/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics

variable (C : Contract)

/-- V2 checked agreement has jointly inhabited inputs for either Boolean. -/
theorem checked_v2_family (v : Bool) (balance : Nat) (hb : balance < Evm.W)
    (bal : Fin Evm.W → Nat) (self : Fin Evm.W) (heq : balance = bal self)
    (frame : Nat) (base : Nat → Fin Evm.W) :
    (Evm.Compiler.Compilation.core (b := 0) _ (fragment_family C v)).AgreesV2
      1 frame base (Evm.freshT C balance hb self) (Evm.Machine.init bal self) := by
  apply Main.compiler_checked_v2
  exact ⟨simulation_family C balance hb bal self heq, by change 1 ≤ Evm.Lmax; decide⟩

/-- V2's actual Main headline yields success for the inhabited require family. -/
theorem correct_v2_success (balance : Nat) (hb : balance < Evm.W)
    (bal : Fin Evm.W → Nat) (self : Fin Evm.W) (heq : balance = bal self) :
    ∃ o mc',
      Prog.run (Evm.freshT C balance hb self) (requireProgram C true) = .ok o ∧
      Evm.run (Evm.compileProg 0 (requireProgram C true)) (Evm.Machine.init bal self) =
        .ok mc' 0 ∧
      Evm.Sim C (1 + Evm.Prog.pushes (requireProgram C true)) 0 (Evm.Frag.init []) o.st mc' :=
  correct_success C balance hb bal self heq

/-- The same inhabited source makes the real checked entry return and run. -/
theorem actual_entry_success (balance : Nat) (hb : balance < Evm.W)
    (bal : Fin Evm.W → Nat) (self : Fin Evm.W) (heq : balance = bal self) :
    ∃ compiled : Evm.Compiler.Compilation 0 (Evm.Frag.init []) (requireProgram C true),
      Evm.Compiler.compile 0 (Evm.Frag.init []) (requireProgram C true) = some compiled ∧
      ∃ mc', Evm.run compiled.code (Evm.Machine.init bal self) = .ok mc' 0 ∧
        mc'.stack = (Evm.Machine.init bal self).stack ∧
        Evm.Sim C (1 + Evm.Prog.pushes (requireProgram C true)) 0 (Evm.Frag.init [])
          (Evm.freshT C balance hb self) mc' :=
  Evm.Compiler.compile_core_success (fragment_family C true)
    (simulation_family C balance hb bal self heq) (by change 1 ≤ Evm.Lmax; decide)
    (source_true C _)

/-- A closed successful actual-entry execution: no feasibility assumption is
left to a caller, and the reused source program has a real require statement. -/
theorem closed_actual_entry_success :
    ∃ compiled : Evm.Compiler.Compilation 0 (Evm.Frag.init []) (requireProgram emptyContract true),
      Evm.Compiler.compile 0 (Evm.Frag.init []) (requireProgram emptyContract true) = some compiled ∧
      ∃ mc', Evm.run compiled.code (Evm.Machine.init (fun _ => 0) ⟨0, by decide⟩) = .ok mc' 0 := by
  obtain ⟨compiled, accepted, mc', execution, _, _⟩ :=
    actual_entry_success emptyContract 0 (by decide) (fun _ => 0) ⟨0, by decide⟩ rfl
  exact ⟨compiled, accepted, mc', execution⟩

/-- info: 'Solidity.Assurance.NonVacuityH28.checked_v2_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_v2_family

/-- info: 'Solidity.Assurance.NonVacuityH28.correct_v2_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms correct_v2_success

/-- info: 'Solidity.Assurance.NonVacuityH28.actual_entry_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms actual_entry_success

/-- info: 'Solidity.Assurance.NonVacuityH28.closed_actual_entry_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms closed_actual_entry_success

end Solidity.Assurance.NonVacuityH28
