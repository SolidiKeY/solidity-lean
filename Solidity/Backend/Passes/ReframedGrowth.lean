import Solidity.Backend.Passes.ReframedCapacity
import Solidity.Backend.Passes.ReframedTripleControls

/-! Transport actual allocator growth across smaller reservations. The original
positive capacity witness supplies the stronger initial invariant; no stronger
invariant is inferred merely from a smaller-frame representation. -/
namespace Solidity.Backend.Passes
open Evm Evm.Memory

theorem allocator_growth_reservation_shrink {C : Contract} {Γ Δ : Ctx}
    {b before after cost budget : Nat} {σ : State C Γ} {τ : State C Δ}
    {base selected : Nat → Fin W} {m out : Machine}
    (growth : GrowsAllocator b before cost σ base m τ selected out)
    (capacity : AllocationInput b before budget σ base m)
    (nonzero : budget ≠ 0) (smaller : after ≤ before) (positive : 0 < after) :
    GrowsAllocator b after cost σ base m τ selected out := by
  rcases capacity with zero | ⟨_,cursor,allocator,_⟩
  · exact False.elim (nonzero zero)
  · intro current hb represented fit
    have same : current = cursor :=
      Word.val.inj (represented.arrays.free.cell.symm.trans allocator.arrays.free.cell)
    subst current
    exact allocator_reservation_shrink (growth cursor hb allocator fit) smaller positive

theorem allocator_growth_reframed_comp {C : Contract} {Γ Δ Ξ : Ctx}
    {b frameA frameB frameC head tail budget : Nat}
    {σ : State C Γ} {τ : State C Δ} {υ : State C Ξ}
    {base middle selected : Nat → Fin W} {m mid out : Machine}
    (first : GrowsAllocator b frameA head σ base m τ middle mid)
    (second : GrowsAllocator b frameB tail τ middle mid υ selected out)
    (capacity : AllocationInput b frameA (head + budget) σ base m)
    (nonzero : budget ≠ 0)
    (smallerAB : frameB ≤ frameA) (smallerBC : frameC ≤ frameB)
    (positiveB : 0 < frameB) (positiveC : 0 < frameC) :
    GrowsAllocator b frameC (head + tail) σ base m υ selected out := by
  have reached : AllocationInput b frameB budget τ middle mid :=
    allocation_input_reservation_shrink (first.nextInput capacity) smallerAB positiveB
  have totalNonzero : head + budget ≠ 0 := by omega
  exact GrowsAllocator.comp
    (allocator_growth_reservation_shrink first capacity totalNonzero
      (Nat.le_trans smallerBC smallerAB) positiveC)
    (allocator_growth_reservation_shrink second reached nonzero smallerBC positiveC)
end Solidity.Backend.Passes

namespace Solidity.Backend.Passes.ReframedGrowthControls
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C initial base machine initial_repr)
open LoopScopeControls

/-- Actual preparation and allocating loop outputs compose at frame5, with the
selected cost and both maps fixed before the arbitrary saved stack tail. -/
theorem reached :
    ∃ (mb nb : Nat → Fin W) (mid next : Machine) (amount : Nat)
      (ext : prepared.st.H <+: loopOut.st.H),
      LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ amount ∧
      ∀ tail,
      MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
        prepared.st {mid with stack := tail} mb ∧
      MappedOutput checked 1 64 mb prepared.st {mid with stack := tail}
        loopOut.st {next with stack := tail} nb ∧
      GrowsAllocator 1 5 (2 + amount) initial base {machine with stack := tail}
        loopOut.st nb {next with stack := tail} := by
  obtain ⟨mb,nb,ob,mid,next,out,amount,ext,cost,sl,sr,hm,hn,ho,all⟩ :=
    ReframedTripleControls.shared
  obtain ⟨_,_,_,_,_,middle,_,_,_,_,_⟩ := all []
  rcases middle with ⟨actual,extension,actualCost,state,baseExtension,growth⟩
  refine ⟨mb,nb,mid,next,actual,extension,actualCost,?_⟩
  intro tail
  obtain ⟨_,_,first,_,_,_,_,_,_,_,_⟩ := all tail
  have actualGrowth : GrowsAllocator 1 64 actual prepared.st mb {mid with stack := tail}
      loopOut.st nb {next with stack := tail} := by
    intro cursor hb allocator fit
    exact (growth cursor hb (allocator.mem_eq rfl) fit).mem_eq rfl
  have capacity : AllocationInput 1 128 (preparation.cert.cost initial + 3)
      initial base {machine with stack := tail} := by
    rw [costs.1]
    exact .inr ⟨by decide,wmod 256,initial_repr.2.mem_eq rfl,by decide +kernel⟩
  refine ⟨first,⟨actual,extension,actualCost,state.stack tail,baseExtension,actualGrowth⟩,?_⟩
  have joined := allocator_growth_reframed_comp (frameC := 5) first.2.2 actualGrowth capacity
    (by decide : (3 : Nat) ≠ 0) (by decide) (by decide) (by decide) (by decide)
  simpa only [costs.1] using joined
end Solidity.Backend.Passes.ReframedGrowthControls

namespace Solidity.Backend.Passes.ReframedGrowthControls
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C initial base machine initial_repr)
open LoopScopeControls

/-- Dropping the middle allocation cost gives the wrong ACTUAL reached cursor,
regardless of the proposed selected object map. -/
theorem skipped_allocation_cost (selected : Nat → Fin W) :
    ¬ GrowsAllocator 1 5 2 initial base machine loopOut.st selected
      LoopScopeTrace.loopTarget := by
  intro growth
  have allocator := allocator_reservation_shrink initial_repr.2
    (by decide : 5 ≤ 128) (by decide : 0 < 5)
  have reached := growth (wmod 256) (by decide) allocator (by decide +kernel)
  have actual : LoopScopeTrace.loopTarget.mem 0 = .val (wmod 261) := by decide +kernel
  have distinct : (Word.val (wmod 261)) ≠ .val (wmod 258) := by decide +kernel
  exact distinct (actual.symm.trans reached.arrays.free.cell)
end Solidity.Backend.Passes.ReframedGrowthControls
