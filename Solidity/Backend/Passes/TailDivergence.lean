import Solidity.Backend.Passes.TailControls

/-! An actual core Compilation reaches intrinsic divergence from a populated,
fresh-state-reachable fixture. Public/session divergence remains open. -/
namespace Solidity.Backend.Passes.TailDivergence
open Solidity.Evm Solidity.Evm.Compiler
open Solidity.Backend.Passes.Controls.Fixture

def spin : Prog C Γ Γ := .cons (.loop .auto (.simple (.bool true)) .nil) .nil
def checked : Compilation 0 (Frag.init Γ) spin := .core (Frag.init Γ) (by rfl)

theorem source_diverges : spin.run σ = .error .diverge := by
  have hl : (Stmt.loop (C := C) (Γ := Γ) .auto (.simple (.bool true)) .nil).run σ =
      .error .diverge := by
    change TLoop.run (fun o : Solidity.Out C σ.H Γ => .ok o)
      (fun _ => .ok true) ⟨σ, List.prefix_refl _⟩ = .error .diverge
    have iter : ∀ (n : Nat) (o : Solidity.Out C σ.H Γ),
        TLoop.iterN (fun o => .ok o) (fun _ => .ok true) n o = .inl o := by
      intro n
      induction n with
      | zero => intro o; rfl
      | succ n ih => intro o; exact ih o
    have hn : ¬ ∃ r n, TLoop.iterN (fun o : Solidity.Out C σ.H Γ => .ok o)
        (fun _ => .ok true) n ⟨σ, List.prefix_refl _⟩ = .inr r := by
      rintro ⟨r, n, hr⟩
      rw [iter] at hr
      cases hr
    unfold TLoop.run
    rw [dif_neg hn]
  exact Prog.run_cons_error hl

theorem input : checked.Input 1 4 base σ machine :=
  ⟨fixture_repr.core, by decide +kernel⟩

private theorem empty_fault : run checked.code {machine with stack := []} = .fault := by
  rcases compilation_exact checked (compilation_input_stack checked input []) rfl with
    ⟨o, m, hs, _, _, _⟩ | ⟨hs | ⟨_, hs⟩, _⟩ | ⟨_, ht⟩
  · rw [source_diverges] at hs
    cases hs
  · rw [source_diverges] at hs
    cases hs
  · rw [source_diverges] at hs
    cases hs
  · exact ht

/-- This exercises the general law's typed fault branch at arbitrary tails. -/
theorem diverges_all_tails (tail : List Word) :
    spin.run σ = .error .diverge ∧
      run checked.code {machine with stack := tail} = .fault := by
  refine ⟨source_diverges, ?_⟩
  rw [compilation_tail_exact checked input rfl tail, empty_fault]
  rfl

theorem actual_recognizer_accepts :
    (Compiler.compile 0 (Frag.init Γ) spin).isSome = true := by decide +kernel

end Solidity.Backend.Passes.TailDivergence
