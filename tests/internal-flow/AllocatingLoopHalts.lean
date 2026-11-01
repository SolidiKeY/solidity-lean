import tests.«internal-flow».AllocatingLoopFacts
namespace Solidity.Backend.InternalFlow.AllocatingLoopHalts
open Evm Evm.Memory PublishedLoops PublishedLoopChecks

/-- This is the real successful prefix BEFORE the explicit failure, not a
State recovered from TRes.error. Its allocations compose with the real call. -/
theorem target_allocation : ∃ m₁ base₁ m₂ base₂,
    run callBefore.code machine = .ok m₁ 0 ∧ run allocationCompiled.code m₁ = .ok m₂ 0 ∧
    StateRepr 1 1 64 allocationCompiled.frag allocated.st base₂ m₂ ∧
    m₂.stack = machine.stack ∧ BaseExtends callMid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 7 (State.init C) bases machine allocated.st base₂ m₂ := by
  obtain ⟨m₁,base₁,hp,hr,hk,he,hg,room⟩ := allocating_prefix_room callBefore (cert true)
    (initial_repr C).1 callPrefix_frame capacity callMid call_prefix_actual (demand_bound true)
  have input : AllocationInput 1 64 ((Calls.plainStmt allocationCompiled).cost callMid.st) callMid.st base₁ m₁ := by
    rw [allocation_cost]; exact hg.nextInput capacity
  obtain ⟨m₂,base₂,ht,hr',hk',he',hg'⟩ := allocation_only hr input
  have total : GrowsAllocator 1 64 7 (State.init C) bases machine allocated.st base₂ m₂ := by
    have h := hg.comp hg'
    rw [callPrefix_cost,allocation_cost] at h
    exact h
  exact ⟨m₁,base₁,m₂,base₂,hp,ht,hr',hk'.trans hk,he',total⟩

theorem target_fault : ∃ m₁ base₁,
    run callBefore.code machine = .ok m₁ 0 ∧
    StateRepr 1 1 64 callBefore.frag callMid.st base₁ m₁ ∧
    m₁.stack = machine.stack ∧ BaseExtends (State.init C).H bases base₁ ∧
    GrowsAllocator 1 64 (callBefore.cost (State.init C)) (State.init C) bases machine callMid.st base₁ m₁ ∧
    run divergingCode m₁ = .fault ∧ run (callBefore.code ++ divergingCode) machine = .fault :=
  after_allocating_prefix_diverge callBefore divergingCert (initial_repr C).1 callPrefix_frame divergence_frame
    capacity callMid call_prefix_actual divergence_demand source_diverges

theorem wrong_divergence_class : run (callBefore.code ++ divergingCode) machine ≠ .revert := by
  obtain ⟨m,base,hp,hr,hk,he,hg,ht,whole⟩ := target_fault
  rw [whole]; intro h; cases h

private theorem uint_word {v : PrimTy.uint.Denote} {w : Word} {n : Fin W}
    (repr : ReprV .uint v w) (value : v.1 = (n.val : Int)) : w = .val n := by
  obtain ⟨a,hw,ha⟩ := repr
  have he : a = n := Fin.ext (Int.ofNat_inj.mp (ha.symm.trans value))
  exact hw.trans (congrArg Word.val he)

def beforeFailureCells (base : Nat → Fin W) (m : Machine) : List Word :=
  [m.mem 1,m.mem (base callPrivate.id).val,m.mem (base returned.id).val,
   m.mem ((base returned.id).val+1),m.mem ((base returned.id).val+1+1),
   m.mem (base fresh.id).val,m.mem ((base fresh.id).val+1),m.mem ((base fresh.id).val+1+1),
   .val (m.store.cells (.root 0)),m.mem 0]

/-- Complete ordered observations on the SAME actual successful allocation
prefix, followed by the actual checked body revert. No failed State is returned. -/
theorem before_failure_observed : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W),
    run callBefore.code machine = .ok m₁ 0 ∧ run allocationCompiled.code m₁ = .ok m₂ 0 ∧
    run bodyCompiled.code m₁ = .revert ∧
    StateRepr 1 1 64 allocationCompiled.frag allocated.st base₂ m₂ ∧
    GrowsAllocator 1 64 7 (State.init C) bases machine allocated.st base₂ m₂ ∧ m₂.stack = [w[77]] ∧
    m₂.mem 3 = .val (base₁ returned.id) ∧ m₂.mem 2 = .val (base₁ returned.id) ∧
    m₂.mem 4 = .val (base₂ fresh.id) ∧
    beforeFailureCells base₂ m₂ = [w[42],w[0],w[2],w[7],w[11],w[2],w[0],w[0],w[9],w[135]] := by
  obtain ⟨m₁,base₁,m₂,base₂,hp,ht,hr,stack,he,grown⟩ := target_allocation
  have first := old_alias (σ := callMid.st) allocated hr he returned (.there .here) old_alias_first
  have second := old_alias (σ := callMid.st) allocated hr he returned (.there (.there .here)) old_alias_second
  obtain ⟨r,hget,hptr⟩ := hr.pointers (.here : Idx (.mem A :: Caller) (.mem A))
  have same : r = fresh := Option.some.inj (hget.symm.trans fresh_alias)
  rw [same] at hptr
  obtain ⟨lp,lr,ln,e0,e1,n0,n1,root,marker⟩ := allocated_values
  have privateLength := (hr.heap.arrays (callPrivate.wk allocated.ext)).length
  rw [lp] at privateLength
  have returnedLength := (hr.heap.arrays (returned.wk allocated.ext)).length
  rw [lr] at returnedLength
  have newLength := (hr.heap.arrays fresh).length
  rw [ln] at newLength
  change m₂.mem (base₂ callPrivate.id).val = w[0] at privateLength
  change m₂.mem (base₂ returned.id).val = w[2] at returnedLength
  have e0' := uint_word ((hr.heap.arrays (returned.wk allocated.ext)).elements 0 _ e0) rfl
  have e1' := uint_word ((hr.heap.arrays (returned.wk allocated.ext)).elements 1 _ e1) rfl
  have n0' := uint_word ((hr.heap.arrays fresh).elements 0 _ n0) rfl
  have n1' := uint_word ((hr.heap.arrays fresh).elements 1 _ n1) rfl
  change m₂.mem ((base₂ returned.id).val+1) = w[7] at e0'
  change m₂.mem ((base₂ returned.id).val+1+1) = w[11] at e1'
  change m₂.mem (base₂ fresh.id).val = w[2] at newLength
  change m₂.mem ((base₂ fresh.id).val+1) = w[0] at n0'
  change m₂.mem ((base₂ fresh.id).val+1+1) = w[0] at n1'
  have mark := hr.core.vals (.there (.there (.there .here)) : Idx (.mem A :: Caller) (.val .uint))
  rw [marker] at mark
  have mark' : m₂.mem 1 = w[42] := uint_word mark rfl
  have stor := hr.core.store "count" (.prim .uint) rfl
  change ReprAt m₂.store 1 (.prim .uint) (rootSlot C "count")
    (allocated.st.storage.get (rfl : C.rootType "count" = some (.prim .uint))) at stor
  rw [root] at stor
  have countCell : (.val (m₂.store.cells (.root 0)) : Word) = w[9] := by
    cases stor with | prim h => exact uint_word h rfl
  have space : (wmod 128).val + 7 < W := by decide +kernel
  have alloc := grown (wmod 128) (by decide) (initial_repr C).2 space
  have cursor : m₂.mem 0 = w[135] := alloc.arrays.free.cell.trans (congrArg Word.val (by
    apply Fin.ext
    change (wmod 128).val+7 = (wmod 135).val
    decide +kernel))
  have bodyHalt : run bodyCompiled.code m₁ = .revert := by
    rw [body_code,run_append_ok ht]
    rfl
  refine ⟨m₁,base₁,m₂,base₂,hp,ht,bodyHalt,hr,grown,stack,first,second,hptr,?_⟩
  simp only [beforeFailureCells,mark',privateLength,returnedLength,newLength,e0',e1',n0',n1',countCell,cursor]

theorem allocation_negatives : ∃ (m₁ : Machine) (m₂ : Machine) (base₂ : Nat → Fin W),
    run callBefore.code machine = .ok m₁ 0 ∧ run allocationCompiled.code m₁ = .ok m₂ 0 ∧
    m₂.mem 3 ≠ .val (base₂ fresh.id) ∧ m₂.mem 0 ≠ w[132] ∧
    beforeFailureCells base₂ m₂ ≠ [w[42],w[0],w[2],w[7],w[11],w[2],w[0],w[0],w[0],w[135]] := by
  obtain ⟨m₁,base₁,m₂,base₂,hp,ht,hf,hr,hg,hk,first,second,newptr,observed⟩ := before_failure_observed
  have separated := hr.heap.separated (returned.wk allocated.ext) fresh (by decide +kernel)
  have different : base₂ returned.id ≠ base₂ fresh.id := by
    intro he
    change (base₂ returned.id).val + 1 + _ ≤ (base₂ fresh.id).val ∨
      (base₂ fresh.id).val + 1 + _ ≤ (base₂ returned.id).val at separated
    rw [he] at separated
    rcases separated with h | h <;> omega
  have alias := old_alias (σ := callMid.st) allocated hr (BaseExtends.refl base₂) returned (.there .here) old_alias_first
  change m₂.mem 3 = .val (base₂ returned.id) at alias
  have cursor := congrArg (fun xs : List Word => xs[9]?) observed
  change some (m₂.mem 0) = some w[135] at cursor
  have cursor' := Option.some.inj cursor
  refine ⟨m₁,m₂,base₂,hp,ht,?_,?_,?_⟩
  · rw [alias]; exact fun h => different (Word.val.inj h)
  · rw [cursor']; decide +kernel
  · rw [observed]; decide +kernel

/-- info: true -/
#guard_msgs in #eval decide (cells (callBefore.code ++ allocationCompiled.code)
  [0,1,2,3,4,63,128,129,130,131,132,133,134] =
  some [w[77],w[135],w[42],w[129],w[129],w[132],w[99],w[0],w[2],w[7],w[11],w[2],w[0],w[0]])

#print axioms allocation_negatives
#print axioms target_fault
#print axioms wrong_divergence_class
#print axioms before_failure_observed
#print axioms target_allocation
end Solidity.Backend.InternalFlow.AllocatingLoopHalts
