import Solidity.Backend.AbiWorld.PublicCompilerTotal

/-! Guard reject-all and always-revert compilers satisfying a conditional contract.
A nonempty supported program has a checked intrinsic-source success, and another
supported program reverts. The public compiler and existing fixed Agrees relation
supply the actual target outcomes at the SAME inhabited simulation input. No
OracleAgrees/output premise is assumed. This is the basic EVM/compiler domain,
not resolved Solidity.Source/callee adequacy or physical P1 frames; gas/fork and
returndata bytes are absent from this machine/outcome interface. -/
namespace Solidity.H62.ReadonlyAudit.CompilerOutcomeWitnesses
open Solidity Solidity.Evm Solidity.Backend.AbiWorld.PublicCompilerTotal

def contract : Contract := { vars := [] }
def initial : State contract [] := freshT contract 0 W_pos ⟨0,W_pos⟩
def machine : Machine := Machine.init (fun _ => 0) ⟨0,W_pos⟩
def program : Prog contract [] [.val .bool] :=
  .cons (.declLocal .bool (.user "flag") (some (.simple (.bool true)))) .nil
def reverting : Prog contract [] [] := .cons .revert .nil

theorem program_ok : ProgOk [] program := .cons (.declSome .bool (.user "flag") (.bool true)) .nil
theorem reverting_ok : ProgOk [] reverting := .cons .revert .nil

theorem source_flag : ∃ o, program.run initial = .ok o ∧ o.st.env.1 = true := ⟨_,rfl,rfl⟩
theorem source_revert : reverting.run initial = .error .revert := rfl

theorem input_sim : Sim contract 1 0 (Frag.init []) initial machine :=
  Sim.init contract 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl

theorem word_horizon : 1 ≤ Lmax := by unfold Lmax; decide

/-- Reuse the fixed public relation: source success with no payment forces target success. -/
theorem success_of_agrees {C : Contract} {Γ Δ : Ctx} {b L frame : Nat} {F : Frag Γ}
    {P : Prog C Γ Δ} (result : Compiler.Compilation b F P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine} (agrees : result.Agrees L frame base σ m)
    (source : ∃ o, P.run σ = .ok o) (nopay : Evm.Prog.pays P = false) :
    ∃ m', Evm.run result.code m = .ok m' 0 := by
  obtain ⟨o, hs⟩ := source
  rcases agrees with ⟨_,m',_,hm,_,_⟩ | ⟨bad,_⟩ | ⟨pays,_,_⟩ | ⟨div,_⟩
  · exact ⟨m',hm⟩
  · rcases bad with bad | ⟨_,bad⟩
    · cases hs.symm.trans bad
    · cases hs.symm.trans bad
  · rw [nopay] at pays
    cases pays
  · cases hs.symm.trans div

/-- Reverting intrinsic-source executions force the actual data-free machine revert. -/
theorem revert_of_agrees {C : Contract} {Γ Δ : Ctx} {b L frame : Nat} {F : Frag Γ}
    {P : Prog C Γ Δ} (result : Compiler.Compilation b F P) {base : Nat → Fin W}
    {σ : State C Γ} {m : Machine} (agrees : result.Agrees L frame base σ m)
    (source : P.run σ = .error .revert) : Evm.run result.code m = .revert := by
  rcases agrees with ⟨_,_,ok,_,_,_⟩ | ⟨_,hm⟩ | ⟨_,hm,_⟩ | ⟨div,_⟩
  · cases source.symm.trans ok
  · exact hm
  · exact hm
  · cases source.symm.trans div

/-- The source program, actual simulation and full fixed observation are jointly met. -/
theorem joint_agreement : ProgOk [] program ∧
    Sim contract 1 0 (Frag.init []) initial machine ∧
    (∃ o, program.run initial = .ok o ∧ o.st.env.1 = true) ∧
    ∃ result, Compiler.compile 0 (Frag.init []) program = some result ∧
      result.Agrees 1 0 (fun _ => ⟨0,W_pos⟩) initial machine := by
  refine ⟨program_ok,input_sim,source_flag,?_⟩
  obtain ⟨result,compiled,agrees⟩ := compile_agrees 0 (Matches.init []) program_ok
  exact ⟨result,compiled,agrees 1 0 (fun _ => ⟨0,W_pos⟩) initial machine input_sim word_horizon⟩

theorem actual_success : ∃ result, Compiler.compile 0 (Frag.init []) program = some result ∧
    ∃ final, Evm.run result.code machine = .ok final 0 := by
  obtain ⟨result,compiled,agrees⟩ := compile_agrees 0 (Matches.init []) program_ok
  refine ⟨result,compiled,success_of_agrees result (L := 1) (frame := 0) (base := fun _ => ⟨0,W_pos⟩) (σ := initial) (m := machine) ?_ ?_ program_ok.quiet.2.1⟩
  · exact agrees 1 0 (fun _ => ⟨0,W_pos⟩) initial machine input_sim word_horizon
  · obtain ⟨o,ran,_⟩ := source_flag
    exact ⟨o,ran⟩

theorem actual_revert : ∃ result, Compiler.compile 0 (Frag.init []) reverting = some result ∧
    Evm.run result.code machine = .revert := by
  obtain ⟨result,compiled,agrees⟩ := compile_agrees 0 (Matches.init []) reverting_ok
  refine ⟨result,compiled,revert_of_agrees result (L := 1) (frame := 0) (base := fun _ => ⟨0,W_pos⟩) (σ := initial) (m := machine) ?_ source_revert⟩
  exact agrees 1 0 (fun _ => ⟨0,W_pos⟩) initial machine input_sim word_horizon

theorem reject_all_refused : Compiler.compile 0 (Frag.init []) program ≠ none := by
  obtain ⟨result,compiled,_⟩ := actual_success
  rw [compiled]
  intro bad
  cases bad

theorem always_revert_refused : ∃ result, Compiler.compile 0 (Frag.init []) program = some result ∧
    Evm.run result.code machine ≠ .revert := by
  obtain ⟨result,compiled,final,ran⟩ := actual_success
  refine ⟨result,compiled,?_⟩
  rw [ran]
  intro bad
  cases bad

theorem constant_revert_control : ¬ ∃ final, (.revert : Evm.Out) = .ok final 0 := by
  rintro ⟨_,bad⟩
  cases bad

end Solidity.H62.ReadonlyAudit.CompilerOutcomeWitnesses
