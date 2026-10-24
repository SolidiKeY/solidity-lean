import Solidity.Evm.MemoryGrowResult

/-!
# Scope exit in the memory simulation

Popping a scope removes its pointer/value locals, while keeping heap growth
and every older local at its existing runtime level. Branches meet the core
storage-alias flags; primitive memory pointers remain initialized in either
branch and keep their typed references.
-/
namespace Solidity.Evm.Memory

variable {C : Contract}

private theorem get_drop {H : HTy} {Γ Δ : Ctx} (h : Ext Γ Δ) (e : TEnv C H Δ)
    {t : LTy} (i : Idx Γ t) : TEnv.get i (TEnv.drop h e) = TEnv.get (i.ext h) e := by
  induction h with
  | refl => rfl
  | push h ih => exact ih e.2

/-- Dropped locals leave the retained locals at their original addresses. -/
theorem StateRepr.drop {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Δ}
    {σ : State C Δ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (e : Ext Γ Δ) :
    StateRepr L b frame (F.restrict Γ) (σ.drop e) base m := by
  constructor
  · exact (h.core.drop e).congrLook (fun i => Look.ofTEnv_drop e σ.env i)
  · exact h.heap
  · intro p i
    obtain ⟨r, hr, hm⟩ := h.pointers (i.ext e)
    refine ⟨r, (get_drop e σ.env i).trans hr, ?_⟩
    simpa only [cellOf, lvl_ext] using hm
  · have he : Δ.length = Γ.length + e.depth := e.length_eq
    have hl : b + Δ.length ≤ frame := h.locals
    omega
  · exact h.structs
  · exact h.separated
  · exact h.refs

theorem StateRepr.meet {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (G : Frag Γ) :
    StateRepr L b frame (F.meet G) σ base m :=
  ⟨h.core.meet G, h.heap, h.pointers, h.locals, h.structs, h.separated, h.refs⟩

theorem StateRepr.meetRight {L b frame : Nat} {Γ : Ctx} {G : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame G σ base m) (F : Frag Γ) :
    StateRepr L b frame (F.meet G) σ base m :=
  Frag.meet_comm G F ▸ h.meet F

end Solidity.Evm.Memory
