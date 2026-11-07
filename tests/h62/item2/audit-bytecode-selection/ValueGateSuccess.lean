import Solidity.Backend.AbiEntry.ValueGate

/-! Actual checked public-compiler totality and whole-machine observation for
its supported value-gate family. These are intrinsic IR outcomes; gas/fork and
source/native origin remain separate. The frozen interfaces are unchanged.
-/
namespace Solidity.H62.BytecodeSelection.ValueGateFixture
open Backend.AbiEntry Evm

/-- The global certificate and actual selected program/result coexist uniformly
in the entire caller machine; failure branches are retained in the conclusion. -/
theorem certificate_and_selected_execution {C : Contract} {Γ : Ctx}
    (base : Nat) (frag : Frag Γ) (payable : Bool) (machine : Machine) :
    ∃ (_certificate : Interface.ValueGateCertificate ValueGate.program)
      (result : Compiler.Compilation base frag (ValueGate.program (C := C) payable)),
      Compiler.compile base frag (ValueGate.program payable) = some result ∧
      run result.code machine =
        if payable || decide (machine.callvalue.val = 0) then .ok machine 0 else .revert := by
  exact ⟨ValueGate.certificate, ValueGate.compiled base frag payable,
    ValueGate.selected base frag payable,
    ValueGate.executed base frag payable _ (ValueGate.selected base frag payable) machine⟩

/-- A concrete inhabited context satisfies ALL explicit execution hypotheses. -/
theorem executed_jointWitness :
    ∃ (result : Compiler.Compilation 7 (Frag.init [.val .uint])
        (ValueGate.program (C := {vars := []}) true)) (machine : Machine),
      Compiler.compile 7 (Frag.init [.val .uint]) (ValueGate.program true) = some result ∧
      run result.code machine = .ok machine 0 := by
  exact ⟨ValueGate.compiled 7 (Frag.init [.val .uint]) true, Machine.init,
    ValueGate.selected 7 (Frag.init [.val .uint]) true,
    ValueGate.executed 7 (Frag.init [.val .uint]) true _
      (ValueGate.selected 7 (Frag.init [.val .uint]) true) Machine.init⟩

/-- Concrete success also uses a nonempty checked nonpayable program. -/
theorem nonempty_checked_success :
    ∃ result : Compiler.Compilation 7 (Frag.init [.val .uint])
        (ValueGate.program (C := {vars := []}) false),
      Compiler.compile 7 (Frag.init [.val .uint]) (ValueGate.program false) = some result ∧
      result.code ≠ [] ∧ run result.code Machine.init = .ok Machine.init 0 := by
  refine ⟨ValueGate.compiled 7 (Frag.init [.val .uint]) false,
    ValueGate.selected 7 (Frag.init [.val .uint]) false, ?_, ?_⟩
  · rw [ValueGate.code]
    intro impossible
    cases impossible
  · exact ValueGate.executed 7 (Frag.init [.val .uint]) false _
      (ValueGate.selected 7 (Frag.init [.val .uint]) false) Machine.init

/-- Explicit reject-all compiler candidate fails supported-family selection. -/
theorem reject_all_fails_selection :
    ¬ (∀ payable : Bool,
      ∃ result : Compiler.Compilation 7 (Frag.init [.val .uint])
        (ValueGate.program (C := {vars := []}) payable),
        (none : Option (Compiler.Compilation 7 (Frag.init [.val .uint])
          (ValueGate.program (C := {vars := []}) payable))) = some result) := by
  intro total
  obtain ⟨result, impossible⟩ := total false
  cases impossible

/-- Always reverting cannot reproduce the actual supported payable program. -/
theorem always_revert_fails_success {C : Contract} {Γ : Ctx}
    (base : Nat) (frag : Frag Γ) (machine : Machine) :
    run [.revert] machine ≠ run (ValueGate.compiled (C := C) base frag true).code machine := by
  rw [ValueGate.executed base frag true _ (ValueGate.selected base frag true) machine]
  intro impossible
  cases impossible

/-- The same nonempty nonpayable program observes nonzero-value rejection. -/
theorem nonzero_checked_failure :
    run (ValueGate.compiled (C := {vars := []}) 7 (Frag.init [.val .uint]) false).code
      {Machine.init with callvalue := wmod 1} = .revert :=
  ValueGate.executed 7 (Frag.init [.val .uint]) false _
    (ValueGate.selected 7 (Frag.init [.val .uint]) false) _

/-- Always reverting also fails the concrete nonempty supported success case. -/
theorem always_revert_fails_nonempty_program :
    run [.revert] Machine.init ≠
      run (ValueGate.compiled (C := {vars := []}) 7 (Frag.init [.val .uint]) false).code Machine.init := by
  rw [ValueGate.executed 7 (Frag.init [.val .uint]) false _
    (ValueGate.selected 7 (Frag.init [.val .uint]) false) Machine.init]
  intro impossible
  cases impossible

#print axioms nonzero_checked_failure
#print axioms always_revert_fails_nonempty_program
#print axioms nonempty_checked_success
#print axioms certificate_and_selected_execution
#print axioms executed_jointWitness
#print axioms reject_all_fails_selection
#print axioms always_revert_fails_success
end Solidity.H62.BytecodeSelection.ValueGateFixture
