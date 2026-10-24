import Solidity.Evm.MemoryAllocSource

/-!
# Memory results with fresh identities

A program may extend the identity-to-address map, but every reference that
existed on entry retains its address. Allocation consumes a source-computed
number of cells. The allocator implication records that exact cursor advance;
it composes with zero-cost statements using their existing simulation.
-/
namespace Solidity.Evm.Memory

variable {C : Contract}

/-- Extending the address map preserves every older typed reference. -/
def BaseExtends (H : HTy) (base base' : Nat → Fin W) : Prop :=
  ∀ {R : RefTy} (r : HRef H R), base' r.id = base r.id

theorem BaseExtends.refl {H : HTy} (base : Nat → Fin W) : BaseExtends H base base :=
  fun _ => rfl

theorem BaseExtends.trans {H H' : HTy} {base base' base'' : Nat → Fin W}
    (e : H <+: H') (h : BaseExtends H base base') (h' : BaseExtends H' base' base'') :
    BaseExtends H base base'' :=
  fun r => (h' (r.wk e)).trans (h r)

/-- Allocator preservation with the exact number of cells consumed. -/
def GrowsAllocator {Γ Δ : Ctx} (b frame cost : Nat) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (τ : State C Δ)
    (base' : Nat → Fin W) (m' : Machine) : Prop :=
  ∀ cursor, 0 < b → StructAllocatorRepr σ.heap base frame cursor m →
    ∀ hspace : cursor.val + cost < W,
      StructAllocatorRepr τ.heap base' frame ⟨cursor.val + cost, hspace⟩ m'

/-- Capacity is needed only when execution reaches an allocation. -/
def AllocationInput {Γ : Ctx} (b frame cost : Nat) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) : Prop :=
  cost = 0 ∨ (0 < b ∧ ∃ cursor, StructAllocatorRepr σ.heap base frame cursor m ∧
    cursor.val + cost < W)

theorem AllocationInput.of_le {Γ : Ctx} {b frame cost budget : Nat}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : AllocationInput b frame budget σ base m) (hle : cost ≤ budget) :
    AllocationInput b frame cost σ base m := by
  rcases h with h | ⟨hb, c, ha, hs⟩
  · exact .inl (by omega)
  · exact .inr ⟨hb, c, ha, by omega⟩

theorem GrowsAllocator.comp {Γ Δ Ξ : Ctx} {b frame head tail : Nat}
    {σ : State C Γ} {τ : State C Δ} {υ : State C Ξ}
    {base base' base'' : Nat → Fin W} {m m' m'' : Machine}
    (h : GrowsAllocator b frame head σ base m τ base' m')
    (h' : GrowsAllocator b frame tail τ base' m' υ base'' m'') :
    GrowsAllocator b frame (head + tail) σ base m υ base'' m'' := by
  intro c hb ha hs
  have hh : c.val + head < W := by omega
  have ht : (c.val + head) + tail < W := by omega
  simpa only [Nat.add_assoc] using h' ⟨c.val + head, hh⟩ hb (h c hb ha hh) ht

theorem GrowsAllocator.nextInput {Γ Δ : Ctx} {b frame head tail : Nat}
    {σ : State C Γ} {τ : State C Δ} {base base' : Nat → Fin W} {m m' : Machine}
    (h : GrowsAllocator b frame head σ base m τ base' m')
    (hi : AllocationInput b frame (head + tail) σ base m) :
    AllocationInput b frame tail τ base' m' := by
  rcases hi with hz | ⟨hb, c, ha, hs⟩
  · exact .inl (by omega)
  · have hh : c.val + head < W := by omega
    exact .inr ⟨hb, ⟨c.val + head, hh⟩, h c hb ha hh, by simpa only [Nat.add_assoc] using hs⟩

/-- Matching execution with a possibly extended address map and exact allocation cost. -/
def GrowingResult {Γ Δ : Ctx} (L b frame cost : Nat) (F : Frag Δ) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (res : TRes (Solidity.Out C σ.H Δ)) (out : Out) : Prop :=
  (∃ o m' base', res = .ok o ∧ out = .ok m' 0 ∧ StateRepr L b frame F o.st base' m' ∧
    m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
    GrowsAllocator b frame cost σ base m o.st base' m') ∨
      (res = .error .revert ∧ out = .revert)

/-- Existing statement proofs provide the zero-allocation case without recompilation. -/
theorem ResultRepr.growing {Γ Δ : Ctx} {L b frame : Nat} {F : Frag Δ} {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine} {res : TRes (Solidity.Out C σ.H Δ)} {out : Out}
    (h : ResultRepr L b frame F σ base m res out) :
    GrowingResult L b frame 0 F σ base m res out := by
  rcases h with ⟨o, m', hs, ht, hr, hk, ha⟩ | ⟨hs, ht⟩
  · refine .inl ⟨o, m', base, hs, ht, hr, hk, BaseExtends.refl base, ?_⟩
    intro c hb hc hspace
    exact ha c hb hc
  · exact .inr ⟨hs, ht⟩

end Solidity.Evm.Memory
