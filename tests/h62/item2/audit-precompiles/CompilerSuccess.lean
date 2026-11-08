import Solidity.Backend.Payments.EntrySuccess
import Solidity.Stipend.Rule

/-! Guards the reject-all/always-revert regression left open by the abstract
stipend obligation. All premises of the actual checked compiler are inhabited
for the existing nonempty `requireValue` program, with an arbitrary saved tail.
This is core execution success, not a metered stipend or fork correspondence. -/
namespace H62.AuditPrecompiles.CompilerSuccess
open Solidity Solidity.Evm

def source (C : Contract) : State C [] :=
  let σ := freshT C 0 (by decide) ⟨0, by decide⟩
  { σ with tx := { σ.tx with msgValue := ⟨1, by decide⟩ } }

def machine (tail : List Word) : Machine :=
  { Machine.init (fun _ => 0) ⟨0, by decide⟩ with
    callvalue := ⟨1, by decide⟩, stack := tail }

theorem fragment (C : Contract) :
    inFragP (Frag.init []) (Stipend.requireValue : Solidity.Prog C [] []) =
      some (Frag.init []) := rfl

theorem represented (C : Contract) (tail : List Word) :
    Sim C 1 0 (Frag.init []) (source C) (machine tail) := by
  have h := Sim.init C 0 (by decide) (fun _ => 0) ⟨0, by decide⟩ rfl
  exact { h with env := ⟨rfl, rfl, rfl, rfl⟩ }

theorem source_success (C : Contract) :
    Solidity.Prog.run (source C) Stipend.requireValue =
      .ok ⟨source C, List.prefix_refl _⟩ := rfl

theorem actual_success (C : Contract) (tail : List Word) :
    ∃ compiled : Compiler.Compilation 0 (Frag.init [])
        (Stipend.requireValue : Solidity.Prog C [] []),
      Compiler.compile 0 (Frag.init []) Stipend.requireValue = some compiled ∧
      ∃ m', run compiled.code (machine tail) = .ok m' 0 ∧
        m'.stack = tail ∧
        Sim C (1 + Prog.pushes (Stipend.requireValue : Solidity.Prog C [] [])) 0
          (Frag.init []) (source C) m' :=
  Compiler.compile_core_success (fragment C) (represented C tail)
    (by change 1 ≤ Lmax; decide) (source_success C)

/-- The V2 contract uses the same jointly inhabited actual compiler input. -/
theorem checked_v2 (C : Contract) (tail : List Word) (frame : Nat)
    (base : Nat → Fin W) :
    (Compiler.Compilation.core (b := 0) (Frag.init []) (fragment C)).AgreesV2
      1 frame base (source C) (machine tail) :=
  Compiler.Compilation.correct_v2 _
    ⟨represented C tail, by change 1 ≤ Lmax; decide⟩

/-- Successful execution preserves the entire machine, including its saved tail. -/
theorem target_preserved (C : Contract) (tail : List Word) :
    ∃ compiled : Compiler.Compilation 0 (Frag.init [])
        (Stipend.requireValue : Solidity.Prog C [] []),
      Compiler.compile 0 (Frag.init []) Stipend.requireValue = some compiled ∧
      run compiled.code (machine tail) = .ok (machine tail) 0 :=
  ⟨.core (Frag.init []) (fragment C), Compiler.compile_core_some (fragment C), rfl⟩

/-- A closed successful instance has a genuinely nonempty saved stack. -/
theorem inhabited_success :
    ∃ (C : Contract) (tail : List Word), tail ≠ [] ∧
      ∃ compiled : Compiler.Compilation 0 (Frag.init [])
          (Stipend.requireValue : Solidity.Prog C [] []),
        Compiler.compile 0 (Frag.init []) Stipend.requireValue = some compiled ∧
        run compiled.code (machine tail) = .ok (machine tail) 0 :=
  ⟨{ vars := [] }, [.val ⟨7, by decide⟩], (by intro impossible; cases impossible),
    target_preserved _ _⟩

/-- The same nonempty body is admitted by the unchanged stipend rule. -/
theorem admitted (C : Contract) :
    (Stipend.rule C).fits ⟨(Stipend.requireValue : Solidity.Prog C [] [])⟩ :=
  Stipend.requireValue_fits

theorem nonempty (C : Contract) :
    (Stipend.requireValue : Solidity.Prog C [] []) ≠ .nil := by
  intro impossible
  cases impossible

theorem reject_all_excluded (C : Contract) :
    Compiler.compile 0 (Frag.init []) (Stipend.requireValue : Solidity.Prog C [] []) ≠ none := by
  rw [Compiler.compile_core_some (fragment C)]
  exact Option.noConfusion

theorem always_revert_excluded (C : Contract) (tail : List Word) :
    ∃ compiled : Compiler.Compilation 0 (Frag.init [])
        (Stipend.requireValue : Solidity.Prog C [] []),
      Compiler.compile 0 (Frag.init []) Stipend.requireValue = some compiled ∧
      run compiled.code (machine tail) ≠ .revert := by
  obtain ⟨compiled, selected, m', success, _, _⟩ := actual_success C tail
  exact ⟨compiled, selected, by rw [success]; intro impossible; cases impossible⟩

/-- The existing source guard really fails when the call value is zero. -/
theorem source_zero_reverts (C : Contract) :
    Solidity.Prog.run (freshT C 0 (by decide) ⟨0, by decide⟩)
      Stipend.requireValue = .error .revert := rfl

/-- Public selection retains the failure branch; an empty-code replacement
would return successfully instead. -/
theorem target_zero_reverts (C : Contract) (tail : List Word) :
    ∃ compiled : Compiler.Compilation 0 (Frag.init [])
        (Stipend.requireValue : Solidity.Prog C [] []),
      Compiler.compile 0 (Frag.init []) Stipend.requireValue = some compiled ∧
      run compiled.code ({ Machine.init (fun _ => 0) ⟨0, by decide⟩ with stack := tail }) =
        .revert :=
  ⟨.core (Frag.init []) (fragment C), Compiler.compile_core_some (fragment C), rfl⟩

/-- info: 'H62.AuditPrecompiles.CompilerSuccess.actual_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms actual_success
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.reject_all_excluded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reject_all_excluded
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.always_revert_excluded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms always_revert_excluded
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.target_zero_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_zero_reverts
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.machine' does not depend on any axioms -/
#guard_msgs in
#print axioms machine
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.fragment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fragment
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms represented
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_success
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.checked_v2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_v2
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.target_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_preserved
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.inhabited_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inhabited_success
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms admitted
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.nonempty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms nonempty
/-- info: 'H62.AuditPrecompiles.CompilerSuccess.source_zero_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_zero_reverts
end H62.AuditPrecompiles.CompilerSuccess
