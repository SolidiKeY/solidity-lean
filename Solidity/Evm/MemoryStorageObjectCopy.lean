import Solidity.Evm.MemoryFixedCompile
import Solidity.Evm.MemoryObjectConstructionCompile

/-! Copy simulations retain full published object ownership and allocator state.
The projected fixed payload is proved from actual typed object words; heap and
memory preservation are derived by execution, never assumed at input. -/
-- Retain the existing typed object-copy proof reductions on Lean 4.35.
set_option backward.isDefEq.respectTransparency false

namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

theorem Objects.StateRepr.fixedCopy {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : Objects.StateRepr L b frame F σ base m) : FixedStateRepr L b frame F σ base m := by
  refine ⟨h.legacy, ?_, fun r => h.heap.owner.above r⟩
  intro p n r
  have ha := h.heap.arrays ArrTy.fixed r
  refine ⟨?_, ?_⟩
  · have hs := ha.space
    simp only [Objects.cells] at hs
    omega
  · intro i v hv
    have he := ha.elements i v (by simpa only [MObj.elems_fixed] using hv)
    simpa only [Objects.ValueRepr, Objects.header, Nat.add_zero] using he

private theorem restoreObjects {H H' : HTy} {hp : Heap H} {hp' : Heap H'}
    {base : Nat → Fin W} {frame : Nat} {m m' : Machine}
    (h : Objects.HeapRepr hp base frame m) (hh : H' = H) (he : HEq hp' hp)
    (hm : m'.mem = m.mem) : Objects.HeapRepr hp' base frame m' := by
  cases hh
  have hpEq := eq_of_heq he
  cases hpEq
  exact h.mem_eq hm

private theorem restoreAllocator {H H' : HTy} {hp : Heap H} {hp' : Heap H'}
    {base : Nat → Fin W} {frame : Nat} {cursor : Fin W} {m m' : Machine}
    (h : Objects.AllocatorRepr hp base frame cursor m) (hh : H' = H) (he : HEq hp' hp)
    (hm : m'.mem = m.mem) : Objects.AllocatorRepr hp' base frame cursor m' := by
  cases hh
  have hpEq := eq_of_heq he
  cases hpEq
  exact h.mem_eq hm

/-- Preserve ownership of all represented objects, including layouts not copied. -/
theorem FixedResult.objects {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    {source : TRes (Solidity.Out C σ.H Δ)} {target : Out}
    (h : Objects.StateRepr L b frame F σ base m)
    (hr : FixedResult L b frame G σ base m source target) :
    Objects.ResultRepr L b frame G σ base m source target := by
  rcases hr with ⟨o, m', ho, ht, hs, hstack, hmem, hH, hheap⟩ | ⟨ho, ht⟩
  · refine .inl ⟨o, m', ho, ht, ?_, hstack, ?_⟩
    · exact ⟨hs.legacy.core, restoreObjects h.heap hH hheap hmem, hs.legacy.pointers, hs.legacy.locals⟩
    · intro cursor hb hal
      exact restoreAllocator hal hH hheap hmem
  · exact .inr ⟨ho, ht⟩

end Solidity.Evm.Memory
