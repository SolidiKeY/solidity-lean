import Solidity.Backend.Passes.MemoryCallControls

namespace Solidity.Backend.Passes.MemoryCallApplication
open Evm Evm.Memory Evm.Compiler MemoryCallControls

theorem allocation_free : Evm.Prog.pushes allocate = 0 := by decide +kernel
theorem consumer_free : Evm.Prog.pushes consume = 0 := by decide +kernel

theorem budget : AllocationInput 1 128 8 initial base machine :=
  .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩

theorem into_call : MappedBoundaryLink (.memory allocation) checked 1 128 base initial machine := by
  apply memory_budgeted_memoryCalls_link allocation producer push_free frame_difference.2
  intro o hs
  have same : first = o := Except.ok.inj (first_source.symm.trans hs)
  subst o
  simpa only [costs.1,costs.2.1] using budget

theorem after_call : ReachedMappedLink (.memory allocation) checked (.memory consumer)
    1 128 base initial machine := by
  intro o mid selected _ _ _
  exact memoryCalls_memory_link producer push_free consumer (by decide +kernel) costs.2.2.2

theorem joined_source :
    ((allocate.join call).join consume).run initial =
      .ok ⟨final.st,(first.ext.trans second.ext).trans final.ext⟩ ∧
    (allocate.join (call.join consume)).run initial =
      .ok ⟨final.st,first.ext.trans (second.ext.trans final.ext)⟩ :=
  triple_source_success initial first_source second_source final_source

/-- All three ACTUAL maps/machines are selected before the arbitrary saved-tail
quantifier, retaining full call/allocator/frame output at BOTH physical links. -/
theorem shared : ∃ (mb nb ob : Nat → Fin W) (mid next out : Machine),
    mid.stack = [] ∧ next.stack = [] ∧ out.stack = [] ∧ ∀ tail,
    run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run producer.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    run consumer.code {next with stack := tail} = .ok {out with stack := tail} 0 ∧
    run ((allocation.code ++ producer.code) ++ consumer.code) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    run (allocation.code ++ (producer.code ++ consumer.code)) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    MappedOutput (.memory allocation) 1 128 base initial {machine with stack := tail}
      first.st {mid with stack := tail} mb ∧
    MappedOutput checked 1 128 mb first.st {mid with stack := tail}
      second.st {next with stack := tail} nb ∧
    MappedOutput (.memory consumer) 1 128 nb second.st {next with stack := tail}
      final.st {out with stack := tail} ob := by
  simpa only [allocation_free,push_free,consumer_free,Nat.add_zero] using
    compilation_triple_shared (.memory allocation) checked (.memory consumer) input rfl
      into_call after_call (by decide +kernel) (by decide +kernel) (by decide +kernel)
      first_source second_source final_source

theorem consumer_cost (σ : State C After) : consumer.cert.cost σ = 0 :=
  allocationCostProg_zero consume costs.2.2.2 σ

/-- A nonempty pre-call heap makes preservation of every original alias
non-vacuous. Total8 is derived from REAL allocator growth2+6+0. -/
theorem resources {tail : List Word} {mb nb ob : Nat → Fin W} {mid next out : Machine}
    (ha : MappedOutput (.memory allocation) 1 128 base initial {machine with stack := tail}
      first.st mid mb)
    (hb : MappedOutput checked 1 128 mb first.st mid second.st next nb)
    (hc : MappedOutput (.memory consumer) 1 128 nb second.st next final.st out ob) :
    BaseExtends first.st.H mb nb ∧ BaseExtends first.st.H mb ob ∧
    GrowsAllocator 1 128 8 initial base {machine with stack := tail} final.st ob out := by
  refine ⟨hb.2.1,Memory.BaseExtends.trans second.ext hb.2.1 hc.2.1,?_⟩
  have hg := ha.2.2.comp (hb.2.2.comp hc.2.2)
  simpa only [costs.1,costs.2.1,consumer_cost] using hg

/-- The caller had an actual old object BEFORE the memory call. -/
theorem old_reference : first.st.H.length = 1 ∧ second.st.H.length = 4 := by decide +kernel

/-- Syntactic source frame estimates omit private expanded call cells. -/
theorem source_frame_refused {selected : Nat → Fin W} {σ : State C Before} {m : Machine} :
    ¬ checked.Input 1 (1 + frameNeedProg call) selected σ m := by
  intro h
  have bounds := h.2.1
  have smaller := frame_difference.1
  change 1 + producer.need ≤ 1 + frameNeedProg call at bounds
  omega

/-- The compiler's ordinary isMemory selector is NOT all heap branches. -/
theorem branch_controls : checked.isMemory = false ∧ checked.isMemoryCalls = true ∧
    checked.usesMemory = true ∧ checked.requiredFrame = producer.need ∧
    checked.allocationCost first.st = 6 := by
  exact ⟨rfl,rfl,rfl,rfl,costs.2.1⟩

end Solidity.Backend.Passes.MemoryCallApplication
