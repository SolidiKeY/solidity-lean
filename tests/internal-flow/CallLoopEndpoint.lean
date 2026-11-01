import tests.«internal-flow».CallLoopFacts

/-! The actual unchanged memory-return-call followed by the scoped loop.
Concrete compiler projections and the reached theorem are imported proof
boundaries; no desired midpoint, representation or preservation is assumed. -/
namespace Solidity.Backend.InternalFlow.PublishedLoopChecks
open Evm Evm.Memory PublishedLoops

/-- Exact reached loop and combined allocation costs on the original witness. -/
theorem call_exact_growth : ∃ m₁ base₁ m₂ base₂ cost,
    run callBefore.code machine = .ok m₁ 0 ∧
    run (callBefore.code ++ callScope.code) machine = .ok m₂ 0 ∧
    LoopScopes.Cost callScope.cert callMid.st callEnd cost ∧ cost = 0 ∧
    StateRepr 1 1 64 callScope.frag callEnd.st base₂ m₂ ∧
    BaseExtends callMid.st.H base₁ base₂ ∧ m₂.stack = machine.stack ∧
    GrowsAllocator 1 64 4 (State.init C) bases machine callEnd.st base₂ m₂ := by
  obtain ⟨m₁,base₁,m₂,base₂,cost,hp,ht,hall,hc,hr,hr',he,hg,stack,hbase,total⟩ := call_target_reached
  have cz : cost = 0 := LoopScopes.cost_nonallocating hc callScope_nonalloc
  have grown : GrowsAllocator 1 64 4 (State.init C) bases machine callEnd.st base₂ m₂ := by
    simpa only [callPrefix_cost,cz,Nat.add_zero] using total
  exact ⟨m₁,base₁,m₂,base₂,cost,hp,hall,hc,cz,hr',he,stack,grown⟩

/-- The original concrete target claim, including both aliases, private-frame
export, exact cost and cursor. This is a kernel theorem, not a runtime vector. -/
theorem call_loop_endpoint : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W) (cost : Nat),
    run callBefore.code machine = .ok m₁ 0 ∧ run (callBefore.code ++ callScope.code) machine = .ok m₂ 0 ∧
    LoopScopes.Cost callScope.cert callMid.st callEnd cost ∧ cost = 0 ∧
    StateRepr 1 1 64 callScope.frag callEnd.st base₂ m₂ ∧ m₂.stack = machine.stack ∧
    GrowsAllocator 1 64 4 (State.init C) bases machine callEnd.st base₂ m₂ ∧
    m₂.mem (cellOf 1 (.here : Idx Caller (.mem A))) = .val (base₁ returned.id) ∧
    m₂.mem (cellOf 1 (.there .here : Idx Caller (.mem A))) = .val (base₁ returned.id) ∧ m₂.mem 0 = w[132] := by
  obtain ⟨m₁,base₁,m₂,base₂,cost,hp,hall,hc,cz,hr,he,stack,grown⟩ := call_exact_growth
  have first := old_alias (σ := callMid.st) callEnd hr he returned .here call_alias_first
  have second := old_alias (σ := callMid.st) callEnd hr he returned (.there .here) call_alias_second
  have space : (wmod 128).val + 4 < W := by decide +kernel
  have alloc := grown (wmod 128) (by decide) (initial_repr C).2 space
  have eq : (⟨(wmod 128).val+4,space⟩ : Fin W) = wmod 132 := by
    apply Fin.ext
    change (wmod 128).val + 4 = (wmod 132).val
    decide +kernel
  exact ⟨m₁,base₁,m₂,base₂,cost,hp,hall,hc,cz,hr,stack,grown,first,second,
    alloc.arrays.free.cell.trans (congrArg Word.val eq)⟩

private theorem uint_word {v : PrimTy.uint.Denote} {w : Word} {n : Fin W}
    (repr : ReprV .uint v w) (value : v.1 = (n.val : Int)) : w = .val n := by
  obtain ⟨a,hw,ha⟩ := repr
  have he : a = n := Fin.ext (Int.ofNat_inj.mp (ha.symm.trans value))
  exact hw.trans (congrArg Word.val he)

/-- Complete live scalar/root and both heap-object contents from the actual
reached StateRepr. The old caller aliases denote the mutated returned object;
the private empty object remains a separate represented object. -/
theorem call_represented_contents {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr 1 1 64 callScope.frag callEnd.st base m) :
    m.mem (base callPrivate.id).val = w[0] ∧
    m.mem (base returned.id).val = w[2] ∧
    m.mem ((base returned.id).val + 1) = w[3] ∧
    m.mem ((base returned.id).val + 1 + 1) = w[4] ∧
    m.mem (cellOf 1 (.there (.there .here) : Idx Caller (.val .uint))) = w[42] ∧
    (.val (m.store.cells (.root 0)) : Word) = w[11] := by
  have privateLength := (repr.heap.arrays (callPrivate.wk callEnd.ext)).length
  rw [call_private_length] at privateLength
  have returnedLength := (repr.heap.arrays (returned.wk callEnd.ext)).length
  rw [call_returned_length] at returnedLength
  have first := (repr.heap.arrays (returned.wk callEnd.ext)).elements 0 _ call_element_first
  have second := (repr.heap.arrays (returned.wk callEnd.ext)).elements 1 _ call_element_second
  have marker := repr.core.vals (.there (.there .here) : Idx Caller (.val .uint))
  rw [call_marker_value] at marker
  have root := repr.core.store "count" (.prim .uint) rfl
  change ReprAt m.store 1 (.prim .uint) (rootSlot C "count")
    (callEnd.st.storage.get (rfl : C.rootType "count" = some (.prim .uint))) at root
  rw [call_count_value] at root
  cases root with
  | prim hroot =>
    refine ⟨privateLength,returnedLength,?_,?_,uint_word marker rfl,?_⟩
    · exact uint_word first rfl
    · exact uint_word second rfl
    · exact uint_word hroot rfl

/-- Ordered actual target observations, with address maps from the same run. -/
def callTargetCells (after : Nat → Fin W) (m : Machine) : List Word :=
  [m.mem (cellOf 1 (.here : Idx Caller (.mem A))),
   m.mem (cellOf 1 (.there .here : Idx Caller (.mem A))),
   m.mem (cellOf 1 (.there (.there .here) : Idx Caller (.val .uint))),
   m.mem (after callPrivate.id).val, m.mem (after returned.id).val,
   m.mem ((after returned.id).val + 1),m.mem ((after returned.id).val + 1 + 1),
   .val (m.store.cells (.root 0)),m.mem 0]

theorem call_complete_endpoint : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W) (cost : Nat),
    run callBefore.code machine = .ok m₁ 0 ∧
    run (callBefore.code ++ callScope.code) machine = .ok m₂ 0 ∧
    LoopScopes.Cost callScope.cert callMid.st callEnd cost ∧ cost = 0 ∧
    StateRepr 1 1 64 callScope.frag callEnd.st base₂ m₂ ∧
    GrowsAllocator 1 64 4 (State.init C) bases machine callEnd.st base₂ m₂ ∧
    m₂.stack = [w[77]] ∧ callTargetCells base₂ m₂ =
      [.val (base₁ returned.id),.val (base₁ returned.id),w[42],w[0],w[2],w[3],w[4],w[11],w[132]] := by
  obtain ⟨m₁,base₁,m₂,base₂,cost,hp,ht,hc,cz,hr,stack,grown,first,second,cursor⟩ := call_loop_endpoint
  obtain ⟨privateLength,returnedLength,x,y,marker,root⟩ := call_represented_contents hr
  refine ⟨m₁,base₁,m₂,base₂,cost,hp,ht,hc,cz,hr,grown,stack,?_⟩
  simp only [callTargetCells,first,second,marker,privateLength,returnedLength,x,y,root,cursor]

/-- Real negative observations on the same successful target witness.
Heap separation rejects exporting the private default object; actual contents,
root, stack and cursor reject old values, early reset and incorrect cost. -/
theorem call_negative_controls : ∃ (m : Machine) (base : Nat → Fin W),
    run (callBefore.code ++ callScope.code) machine = .ok m 0 ∧
    m.mem (cellOf 1 (.here : Idx Caller (.mem A))) ≠ .val (base callPrivate.id) ∧
    m.mem ((base returned.id).val + 1) ≠ w[7] ∧
    (.val (m.store.cells (.root 0)) : Word) ≠ w[9] ∧
    m.mem 0 ≠ w[131] ∧ m.stack ≠ [w[78]] ∧
    callBefore.cost (State.init C) ≠ 3 := by
  obtain ⟨m₁,base₁,m₂,base₂,cost,hp,ht,hc,cz,hr,stack,grown,first,second,cursor⟩ := call_loop_endpoint
  obtain ⟨privateLength,returnedLength,x,y,marker,root⟩ := call_represented_contents hr
  have separated := hr.heap.separated (callPrivate.wk callEnd.ext) (returned.wk callEnd.ext) (by decide +kernel)
  have different : base₂ returned.id ≠ base₂ callPrivate.id := by
    intro he
    change (base₂ callPrivate.id).val + 1 + _ ≤ (base₂ returned.id).val ∨
      (base₂ returned.id).val + 1 + _ ≤ (base₂ callPrivate.id).val at separated
    rw [he] at separated
    rcases separated with h | h <;> omega
  have live := old_alias (σ := callMid.st) callEnd hr (BaseExtends.refl base₂) returned .here call_alias_first
  refine ⟨m₂,base₂,ht,?_,?_,?_,?_,?_,?_⟩
  · rw [live]; exact fun h => different (Word.val.inj h)
  · rw [x]; decide +kernel
  · rw [root]; decide +kernel
  · rw [cursor]; decide +kernel
  · rw [stack]; decide +kernel
  · rw [callPrefix_cost]; decide +kernel

/-- Original Work5 preparation: actual target bare revert after the
nontrivial allocating call prefix, with no failed State reconstructed. -/
theorem call_rejected_target : run (callBefore.code ++ callRejected.code) machine = .revert := by
  obtain ⟨m₁,base₁,m₂,base₂,cost,hp,ht,hall,hc,hr,rest⟩ := call_target_reached
  rw [run_append_ok hp]
  exact scoped_revert callRejected.cert hr call_rejected_frame
    (LoopScopes.room_nonallocating _ call_rejected_nonalloc _ _ _) call_rejected_source

theorem call_rejected_not_fault : run (callBefore.code ++ callRejected.code) machine ≠ .fault := by
  rw [call_rejected_target]
  intro h
  cases h

#print axioms call_rejected_target
#print axioms call_rejected_not_fault
#print axioms call_complete_endpoint
#print axioms call_negative_controls
#print axioms call_represented_contents
#print axioms call_loop_endpoint
#print axioms call_exact_growth
end Solidity.Backend.InternalFlow.PublishedLoopChecks
