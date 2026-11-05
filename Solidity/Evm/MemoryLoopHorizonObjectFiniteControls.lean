import Solidity.Evm.MemoryLoopHorizonObjectFinite
import Solidity.Evm.MemoryObjectArrayExamples

/-! Inhabited strong finite-horizon transport over the existing populated fixed-
parent heap, for constant exit and spinning conditions. The nil body allocates
nothing. This supplies no allocating-loop capacity or compiler selection claim. -/
namespace Solidity.Evm.Memory.HorizonObjectFiniteControls
open Construction

def cert {C : Contract} {Γ : Ctx} (b : Nat) (truth : Bool) :
    Construction.LoopCert b (Frag.init Γ) (.simple (.bool truth) : Val C Γ .bool)
      .nil (Evm.compileVal b (.simple (.bool truth) : Val C Γ .bool)) [] :=
  ⟨.core _ rfl, Frag.init Γ, .nil _, by simp only [Frag.restrict, Nat.sub_self, List.drop_zero]⟩

theorem represented {C : Contract} {Γ : Ctx} {L b frame : Nat}
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + Γ.length ≤ frame) (truth : Bool) (n : Nat) :
    Construction.CountedHorizonRelation L b frame (Frag.init Γ)
      (.simple (.bool truth)) .nil state base machine n
      (TLoop.iterN (horizonBody (.nil : Prog C Γ Γ))
        (fun o => (.simple (.bool truth) : Val C Γ .bool).evalT o.st)
        n ⟨state,List.prefix_refl _⟩)
      (loopIterN (fun m => exec (Evm.compileVal b (.simple (.bool truth) : Val C Γ .bool)) 0 m)
        (fun m => exec [] 0 m) n machine) := by
  apply (cert b truth).correct_finite_horizon n repr capacity
  intro reached cost turns hp within condition
  exact .inl (by rw [hp.cost_zero (by rfl)]; rfl)

theorem populated_horizons (truth : Bool) (n : Nat) :
    ∃ (C : Contract) (Γ : Ctx) (state : State C Γ) (base : Nat → Fin W) (machine : Machine),
      Construction.CountedHorizonRelation 1 1 8 (Frag.init Γ)
        (.simple (.bool truth)) .nil state base machine n
        (TLoop.iterN (horizonBody (.nil : Prog C Γ Γ))
          (fun o => (.simple (.bool truth) : Val C Γ .bool).evalT o.st)
          n ⟨state,List.prefix_refl _⟩)
        (loopIterN (fun m => exec (Evm.compileVal 1 (.simple (.bool truth) : Val C Γ .bool)) 0 m)
          (fun m => exec [] 0 m) n machine) ∧
      state.H.length=3 ∧ machine.stack=[w[77]] := by
  have h := represented ObjectArrayExamples.initial_repr (by decide +kernel) truth n
  exact ⟨_,_,_,_,_,h,rfl,rfl⟩

end Solidity.Evm.Memory.HorizonObjectFiniteControls
