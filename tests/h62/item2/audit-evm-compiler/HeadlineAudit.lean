import Solidity.Evm.Correct
import tests.h62.item2.«audit-evm-compiler».SuccessAudit

/-! Simultaneous fixtures for the five unchanged intrinsic compiler headlines.
The witness is one nonempty admitted storage-write program. -/
namespace Solidity.H62.EvmCompilerAudit
open Evm Evm.Examples

abbrev source : State StandardExample [] := freshT StandardExample 0 W_pos ⟨0, W_pos⟩
abbrev outputFrag : Frag [] := (inFragP (Frag.init []) setAge).get supported_setAge

theorem admitted : inFragP (Frag.init []) setAge = some outputFrag :=
  (Option.some_get supported_setAge).symm

theorem represented : Sim StandardExample 1 0 (Frag.init []) source fresh :=
  Sim.init StandardExample 0 W_pos fresh.bal ⟨0, W_pos⟩ rfl

theorem compile_correct_joint : ∃ F : Frag [],
    inFragP (Frag.init []) setAge = some F ∧
    Sim StandardExample 1 0 (Frag.init []) source fresh ∧
    1 + Prog.pushes setAge ≤ Lmax :=
  ⟨outputFrag, admitted, represented, by decide +kernel⟩

theorem compile_exact_joint : ∃ F : Frag [],
    inFragP (Frag.init []) setAge = some F ∧
    Sim StandardExample 1 0 (Frag.init []) source fresh ∧
    1 + Prog.pushes setAge ≤ Lmax ∧ Prog.pays setAge = false :=
  ⟨outputFrag, admitted, represented, by decide +kernel, by decide +kernel⟩

theorem compile_box_joint : ∃ (F : Frag []) (final : Machine),
    inFragP (Frag.init []) setAge = some F ∧
    Sim StandardExample 1 0 (Frag.init []) source fresh ∧
    1 + Prog.pushes setAge ≤ Lmax ∧ run (compileProg 0 setAge) fresh = .ok final 0 := by
  obtain ⟨code, codeEq, final, execution, _⟩ := compiled_setAge_writes
  cases Option.some.inj codeEq
  exact ⟨outputFrag, final, admitted, represented, by decide +kernel, execution⟩

theorem compile_net_joint : ∃ (F : Frag []) (final : Machine),
    inFragP (Frag.init []) setAge = some F ∧
    Sim StandardExample 1 0 (Frag.init []) source fresh ∧
    1 + Prog.pushes setAge ≤ Lmax ∧ run (compileProg 0 setAge) fresh = .ok final 0 :=
  compile_box_joint

theorem compile_storage_joint : ∃ (F : Frag []) (balance : Nat)
    (bal : Fin W → Nat) (self : Fin W),
    inFragP (Frag.init []) setAge = some F ∧ Prog.pushes setAge < Lmax ∧
    balance < W ∧ balance = bal self :=
  ⟨outputFrag, 0, fresh.bal, ⟨0, W_pos⟩, admitted, by decide +kernel, W_pos, rfl⟩

/-- All premises of the additive success transfer also have one joint instance. -/
theorem source_success_joint : ∃ (F : Frag []) (out : Solidity.Out StandardExample [] []),
    inFragP (Frag.init []) setAge = some F ∧
    Sim StandardExample 1 0 (Frag.init []) source fresh ∧
    1 + Prog.pushes setAge ≤ Lmax ∧ Prog.pays setAge = false ∧
    Solidity.Prog.run source setAge = .ok out := by
  obtain ⟨F, final, hP, hm, hL, execution⟩ := compile_box_joint
  obtain ⟨out, sourceEq, _⟩ := compile_box hP hm hL execution
  exact ⟨F, out, hP, hm, hL, by decide +kernel, sourceEq⟩

/-- This transfers source success; it assumes no totality for all admitted programs. -/
theorem compile_success_of_source_success
    {C : Contract} {Γ Γ' : Ctx} {L b : Nat} {F : Frag Γ} {F' : Frag Γ'}
    {P : Solidity.Prog C Γ Γ'} {σ : State C Γ} {m : Machine}
    {o : Solidity.Out C σ.H Γ'}
    (hP : inFragP F P = some F') (hm : Sim C L b F σ m)
    (hL : L + Prog.pushes P ≤ Lmax) (hpay : Prog.pays P = false)
    (hsource : Solidity.Prog.run σ P = .ok o) :
    ∃ final, run (compileProg b P) m = .ok final 0 ∧ final.stack = m.stack ∧
      Sim C (L + Prog.pushes P) b F' o.st final := by
  rcases compile_exact hP hm hL hpay with
    ⟨out, final, sourceEq, targetEq, stackEq, finalSim⟩ | ⟨failure, _⟩ | ⟨diverges, _⟩
  · have same : out = o := Except.ok.inj (sourceEq.symm.trans hsource)
    subst out
    exact ⟨final, targetEq, stackEq, finalSim⟩
  · rcases failure with reverted | ⟨_, panicked⟩
    · rw [hsource] at reverted; cases reverted
    · rw [hsource] at panicked; cases panicked
  · rw [hsource] at diverges; cases diverges

#print axioms admitted
#print axioms represented
#print axioms compile_correct_joint
#print axioms compile_exact_joint
#print axioms compile_box_joint
#print axioms compile_net_joint
#print axioms compile_storage_joint
#print axioms source_success_joint
#print axioms compile_success_of_source_success
end Solidity.H62.EvmCompilerAudit
