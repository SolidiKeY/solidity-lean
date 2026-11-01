import tests.«internal-flow».SuccessfulLoopFacts

/-! Actual completed allocating-loop suffix after the unchanged real call.
Every target midpoint and allocator input is derived by the published adapters. -/
namespace Solidity.Backend.InternalFlow.SuccessfulLoop
open Evm Evm.Memory PublishedLoops PublishedLoopChecks

theorem reached : ∃ m₁ base₁ m₂ base₂ amount,
    run callBefore.code machine = .ok m₁ 0 ∧ run (code true) m₁ = .ok m₂ 0 ∧
    run (callBefore.code ++ code true) machine = .ok m₂ 0 ∧
    LoopScopes.Cost (cert true) callMid.st finalOut amount ∧
    StateRepr 1 1 64 callBefore.frag callMid.st base₁ m₁ ∧
    StateRepr 1 1 64 callBefore.frag finalOut.st base₂ m₂ ∧
    BaseExtends callMid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 amount callMid.st base₁ m₁ finalOut.st base₂ m₂ ∧
    m₂.stack = machine.stack ∧ BaseExtends (State.init C).H bases base₂ ∧
    GrowsAllocator 1 64 (callBefore.cost (State.init C) + amount)
      (State.init C) bases machine finalOut.st base₂ m₂ :=
  after_allocating_prefix callBefore (cert true) (initial_repr C).1 callPrefix_frame (frame true)
    total_capacity callMid call_prefix_actual (demand_bound true) finalOut source_run

theorem endpoint : ∃ m₁ base₁ m₂ base₂,
    run callBefore.code machine = .ok m₁ 0 ∧ run (code true) m₁ = .ok m₂ 0 ∧
    run (callBefore.code ++ code true) machine = .ok m₂ 0 ∧
    LoopScopes.Cost (cert true) callMid.st finalOut 3 ∧
    StateRepr 1 1 64 callBefore.frag finalOut.st base₂ m₂ ∧
    BaseExtends callMid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 7 (State.init C) bases machine finalOut.st base₂ m₂ ∧
    m₂.stack = [w[77]] ∧ m₂.mem 0 = w[135] := by
  obtain ⟨m₁,base₁,m₂,base₂,amount,hp,hl,whole,hc,hr,hr',he,hg,stack,he',total⟩ := reached
  have hc' : amount = 3 := exact_cost hc
  subst amount
  have grown : GrowsAllocator 1 64 7 (State.init C) bases machine finalOut.st base₂ m₂ := by
    rw [callPrefix_cost] at total
    exact total
  have space : (wmod 128).val + 7 < W := by decide +kernel
  have allocator := grown (wmod 128) (by decide) (initial_repr C).2 space
  have cursor : m₂.mem 0 = w[135] := allocator.arrays.free.cell.trans (congrArg Word.val (by
    apply Fin.ext
    change (wmod 128).val + 7 = (wmod 135).val
    decide +kernel))
  exact ⟨m₁,base₁,m₂,base₂,hp,hl,whole,hc,hr',he,grown,stack,cursor⟩

private theorem uint_word {v : PrimTy.uint.Denote} {w : Word} {n : Fin W}
    (repr : ReprV .uint v w) (value : v.1 = (n.val : Int)) : w = .val n := by
  obtain ⟨a,hw,ha⟩ := repr
  have he : a = n := Fin.ext (Int.ofNat_inj.mp (ha.symm.trans value))
  exact hw.trans (congrArg Word.val he)

/-- Live caller locals followed by EVERY represented object, root and cursor.
The dropped private local is absent from the final Caller context. -/
def finalCells (base : Nat → Fin W) (m : Machine) : List Word :=
  [m.mem 1,m.mem (base callPrivate.id).val,m.mem (base returned.id).val,
   m.mem ((base returned.id).val+1),m.mem ((base returned.id).val+1+1),
   m.mem (base fresh.id).val,m.mem ((base fresh.id).val+1),m.mem ((base fresh.id).val+1+1),
   .val (m.store.cells (.root 0)),m.mem 0]

theorem complete_endpoint : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W),
    run callBefore.code machine = .ok m₁ 0 ∧ run (code true) m₁ = .ok m₂ 0 ∧
    run (callBefore.code ++ code true) machine = .ok m₂ 0 ∧
    LoopScopes.Cost (cert true) callMid.st finalOut 3 ∧
    StateRepr 1 1 64 callBefore.frag finalOut.st base₂ m₂ ∧ BaseExtends callMid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 7 (State.init C) bases machine finalOut.st base₂ m₂ ∧ m₂.stack = [w[77]] ∧
    m₂.mem 3 = .val (base₁ returned.id) ∧ m₂.mem 2 = .val (base₁ returned.id) ∧
    finalCells base₂ m₂ = [w[0],w[0],w[2],w[7],w[11],w[2],w[0],w[0],w[9],w[135]] := by
  obtain ⟨m₁,base₁,m₂,base₂,hp,hl,whole,hc,hr,he,hg,stack,cursor⟩ := endpoint
  have first : m₂.mem 3 = .val (base₁ returned.id) :=
    old_alias (σ := callMid.st) finalOut hr he returned .here alias_first
  have second : m₂.mem 2 = .val (base₁ returned.id) :=
    old_alias (σ := callMid.st) finalOut hr he returned (.there .here) alias_second
  obtain ⟨lp,lr,ln,e0,e1,n0,n1,root,marker⟩ := final_values
  have p := (hr.heap.arrays (callPrivate.wk finalOut.ext)).length
  rw [lp] at p
  change m₂.mem (base₂ callPrivate.id).val = w[0] at p
  have r := (hr.heap.arrays (returned.wk finalOut.ext)).length
  rw [lr] at r
  change m₂.mem (base₂ returned.id).val = w[2] at r
  have n := (hr.heap.arrays fresh).length
  rw [ln] at n
  change m₂.mem (base₂ fresh.id).val = w[2] at n
  have x := uint_word ((hr.heap.arrays (returned.wk finalOut.ext)).elements 0 _ e0) rfl
  have y := uint_word ((hr.heap.arrays (returned.wk finalOut.ext)).elements 1 _ e1) rfl
  have a := uint_word ((hr.heap.arrays fresh).elements 0 _ n0) rfl
  have b := uint_word ((hr.heap.arrays fresh).elements 1 _ n1) rfl
  change m₂.mem ((base₂ returned.id).val+1) = w[7] at x
  change m₂.mem ((base₂ returned.id).val+1+1) = w[11] at y
  change m₂.mem ((base₂ fresh.id).val+1) = w[0] at a
  change m₂.mem ((base₂ fresh.id).val+1+1) = w[0] at b
  have mark := hr.core.vals (.there (.there .here) : Idx Caller (.val .uint))
  rw [marker] at mark
  have mark' : m₂.mem 1 = w[0] := uint_word mark rfl
  have stor := hr.core.store "count" (.prim .uint) rfl
  change ReprAt m₂.store 1 (.prim .uint) (rootSlot C "count")
    (finalOut.st.storage.get (rfl : C.rootType "count" = some (.prim .uint))) at stor
  rw [root] at stor
  have countCell : (.val (m₂.store.cells (.root 0)) : Word) = w[9] := by
    cases stor with | prim h => exact uint_word h rfl
  refine ⟨m₁,base₁,m₂,base₂,hp,hl,whole,hc,hr,he,hg,stack,first,second,?_⟩
  simp only [finalCells,mark',p,r,n,x,y,a,b,countCell,cursor]

/-- The caller really continues after completed loop-local unwind, reusing
its old aliases and the dropped local's physical cell for a scalar result. -/
theorem next_use : ∃ (m : Machine) (base : Nat → Fin W),
    run ((callBefore.code ++ code true) ++ checkedUse.code) machine = .ok m 0 ∧
    StateRepr 1 1 64 checkedUse.frag usedOut.st base m ∧
    GrowsAllocator 1 64 7 (State.init C) bases machine usedOut.st base m ∧
    m.stack = [w[77]] ∧ m.mem 4 = w[99] ∧ m.mem 0 = w[135] ∧
    m.mem ((base returned.id).val+1+1) = w[99] ∧
    m.mem ((base fresh.id).val+1) = w[0] := by
  obtain ⟨m₁,base₁,m₂,base₂,hp,hl,whole,hc,hr,he,hg,stack,cursor⟩ := endpoint
  obtain ⟨m₃,base₃,ht,hr',hk,he',hg'⟩ := PublishedDirectCalls.program_endpoint checkedUse
    hr use_frame (.inl use_cost) usedOut use_source
  have total : GrowsAllocator 1 64 7 (State.init C) bases machine usedOut.st base₃ m₃ := by
    have h := hg.comp hg'
    rw [use_cost,Nat.add_zero] at h
    exact h
  have result := hr'.core.vals (.here : Idx After (.val .uint))
  rw [use_result] at result
  have result' : m₃.mem 4 = w[99] := uint_word result rfl
  have space : (wmod 128).val + 7 < W := by decide +kernel
  have allocator := total (wmod 128) (by decide) (initial_repr C).2 space
  have cursor' : m₃.mem 0 = w[135] := allocator.arrays.free.cell.trans (congrArg Word.val (by
    apply Fin.ext
    change (wmod 128).val + 7 = (wmod 135).val
    decide +kernel))
  have re := (hr'.heap.arrays ((returned.wk finalOut.ext).wk usedOut.ext)).elements 1 _ use_elements.1
  have fr := (hr'.heap.arrays (fresh.wk usedOut.ext)).elements 0 _ use_elements.2
  have re' : m₃.mem ((base₃ returned.id).val+1+1) = w[99] := uint_word re rfl
  have fr' : m₃.mem ((base₃ fresh.id).val+1) = w[0] := uint_word fr rfl
  refine ⟨m₃,base₃,?_,hr',total,hk.trans stack,result',cursor',re',fr'⟩
  rw [run_append_ok whole]
  exact ht

theorem negative_controls : ∃ (m : Machine) (base : Nat → Fin W),
    run (callBefore.code ++ code true) machine = .ok m 0 ∧
    m.mem 3 ≠ .val (base fresh.id) ∧ m.mem 0 ≠ w[132] ∧
    ¬ GrowsAllocator 1 64 4 (State.init C) bases machine finalOut.st base m ∧
    finalCells base m ≠ [w[0],w[0],w[2],w[3],w[11],w[2],w[0],w[0],w[9],w[135]] ∧
    finalCells base m ≠ [w[0],w[0],w[2],w[7],w[11],w[2],w[0],w[0],w[11],w[135]] ∧
    finalCells base m ≠ [w[42],w[0],w[2],w[7],w[11],w[2],w[0],w[0],w[9],w[135]] := by
  obtain ⟨m₁,base₁,m₂,base₂,hp,hl,whole,hc,hr,he,hg,stack,first,second,observed⟩ := complete_endpoint
  have separated := hr.heap.separated (returned.wk finalOut.ext) fresh (by decide +kernel)
  have different : base₂ returned.id ≠ base₂ fresh.id := by
    intro eq
    change (base₂ returned.id).val + 1 + _ ≤ (base₂ fresh.id).val ∨
      (base₂ fresh.id).val + 1 + _ ≤ (base₂ returned.id).val at separated
    rw [eq] at separated
    rcases separated with h | h <;> omega
  have alias : m₂.mem 3 = .val (base₂ returned.id) :=
    old_alias (σ := callMid.st) finalOut hr (BaseExtends.refl base₂) returned .here alias_first
  have cursor := congrArg (fun xs : List Word => xs[9]?) observed
  change some (m₂.mem 0) = some w[135] at cursor
  have cursor' := Option.some.inj cursor
  refine ⟨m₂,base₂,whole,?_,?_,?_,?_,?_,?_⟩
  · rw [alias]; exact fun h => different (Word.val.inj h)
  · rw [cursor']; decide +kernel
  · intro bad
    have space : (wmod 128).val + 4 < W := by decide +kernel
    have wrong := bad (wmod 128) (by decide) (initial_repr C).2 space
    have eq := cursor'.symm.trans wrong.arrays.free.cell
    have wordEq : (.val ⟨(wmod 128).val+4,space⟩ : Word) = w[132] := congrArg Word.val (by
      apply Fin.ext
      change (wmod 128).val+4 = (wmod 132).val
      decide +kernel)
    have ne : w[135] ≠ w[132] := by
      intro h
      have bad := congrArg Fin.val (Word.val.inj h)
      change 135 = 132 at bad
      omega
    exact ne (eq.trans wordEq)
  · rw [observed]; decide +kernel
  · rw [observed]; decide +kernel
  · rw [observed]; decide +kernel

theorem success_not_failure : run (callBefore.code ++ code true) machine ≠ .revert ∧
    run (callBefore.code ++ code true) machine ≠ .fault := by
  obtain ⟨m₁,base₁,m₂,base₂,hp,hl,whole,rest⟩ := endpoint
  rw [whole]
  constructor <;> intro h <;> cases h

/-- info: true -/
#guard_msgs in #eval decide (cells (callBefore.code ++ code true)
  [0,1,2,3,4,63,128,129,130,131,132,133,134] =
  some [w[77],w[135],w[0],w[129],w[129],w[132],w[99],w[0],w[2],w[7],w[11],w[2],w[0],w[0]])
/-- info: true -/
#guard_msgs in #eval decide (cells ((callBefore.code ++ code true) ++ checkedUse.code)
  [0,1,2,3,4,63,128,129,130,131,132,133,134] =
  some [w[77],w[135],w[0],w[129],w[129],w[99],w[99],w[0],w[2],w[7],w[99],w[2],w[0],w[0]])

#print axioms negative_controls
#print axioms success_not_failure
#print axioms next_use
#print axioms complete_endpoint
#print axioms reached
#print axioms endpoint
end Solidity.Backend.InternalFlow.SuccessfulLoop
