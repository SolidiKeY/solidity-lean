import Solidity.Backend.Passes.Divergence
import Solidity.Backend.Passes.TailDivergence

/-! The same finite-iteration argument as TailDivergence, generalized over
its actual intrinsic state and fragment. No noncomputable loop evaluation. -/
namespace Solidity.Backend.Passes.Spin
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {Γ : Ctx}
def program : Prog C Γ Γ := .cons (.loop .auto (.simple (.bool true)) .nil) .nil

theorem iter (σ : State C Γ) (n : Nat) (o : Solidity.Out C σ.H Γ) :
    TLoop.iterN (fun o => .ok o) (fun _ => .ok true) n o = .inl o := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem diverges (σ : State C Γ) : program.run σ = .error .diverge := by
  have hl : (Stmt.loop (C := C) (Γ := Γ) .auto (.simple (.bool true)) .nil).run σ =
      .error .diverge := by
    change TLoop.run (fun o : Solidity.Out C σ.H Γ => .ok o)
      (fun _ => .ok true) ⟨σ, List.prefix_refl _⟩ = .error .diverge
    have hn : ¬ ∃ r n, TLoop.iterN (fun o : Solidity.Out C σ.H Γ => .ok o)
        (fun _ => .ok true) n ⟨σ, List.prefix_refl _⟩ = .inr r := by
      rintro ⟨r, n, hr⟩
      rw [iter] at hr
      cases hr
    unfold TLoop.run
    rw [dif_neg hn]
  exact Prog.run_cons_error hl

def checked (b : Nat) (F : Frag Γ) : Compilation b F (program (C := C)) :=
  .core F (by simp only [program, inFragP, inFrag, valIn, Frag.restrict,
    Nat.sub_self, List.drop_zero, simpleIn, Evm.Prog.pushes, Evm.Prog.pays, Evm.Prog.shrinks]; rfl)

/-- Exact same loop as the earlier populated fixture, not a new semantics. -/
theorem existing_program : (program (C := Controls.Fixture.C) (Γ := Controls.Fixture.Γ)) =
    TailDivergence.spin := rfl

/-- A represented memory output supplies the core loop's actual Input.
Its complete core projection already contains the reached level bound. -/
theorem memory_link {b L frame : Nat} {Δ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} (a : Memory.CompiledProg b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    :
    MappedBoundaryLink (.memory a) (checked b a.frag) L frame base σ m := by
  intro o mid mb _ _ ha
  exact ⟨ha.1.core, by simpa only [checked, program, Evm.Prog.pushes, Evm.Stmt.pushes,
    Nat.add_zero] using ha.1.core.bound⟩

/-- Later Inputs are unreachable because this actual source program has no
successful result. This is not a bridge from a bare core Sim to memory. -/
theorem unreachable_link {b L frame : Nat} {Δ : Ctx} {F : Frag Γ}
    {Q : Prog C Γ Δ} (suffix : Compilation b (checked (C := C) b F).frag Q)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    MappedBoundaryLink (checked (C := C) b F) suffix L frame base σ m := by
  intro o mid mb hs _ _
  rw [diverges σ] at hs
  cases hs

/-- Arbitrary tails follow typed Input transport, not a raw fault-tail rule. -/
theorem fault_all_tails {b L frame : Nat} {F : Frag Γ}
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : (checked (C := C) b F).Input L frame base σ m) (tail : List Word) :
    run (checked (C := C) b F).code {m with stack := tail} = .fault :=
  (compilation_fault_iff (checked (C := C) b F)
    (compilation_input_stack (checked (C := C) b F) hi tail) rfl).mpr (diverges σ)

end Solidity.Backend.Passes.Spin
