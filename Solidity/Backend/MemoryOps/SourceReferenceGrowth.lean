import Solidity.Backend.MemoryOps.SourceNestedMemory
import Solidity.Backend.MemoryOps.SourceStructGrowth

/-! Operation-side growth of the existing finite reference-parent/Bool-child
observer. Actual Source.allocRef and intrinsic Heap.alloc only; no reference
constructor, alternate graph, injectivity or target allocator is introduced. -/
namespace Solidity.Backend.MemoryOps

private theorem memory_array_congr {D : Source.Layout} {τ : Source.STy} {n m : Nat}
    (h : n=m) (xs : Fin n → Source.Data D τ) (ys : Fin m → Source.Data D τ)
    (he : ∀ i (hi : i<n) (hj : i<m),xs ⟨i,hi⟩=ys ⟨i,hj⟩) :
    (Source.Data.array n (fun _ h => by cases h) xs : Source.Data D (.array .memory τ none))=
      Source.Data.array m (fun _ h => by cases h) ys := by
  first
  | solve | rfl | simp only [] | omega
  | cases h
    have hf : xs=ys := by funext i;exact he i.val i.isLt i.isLt
    cases hf
    rfl

/-- Source pointers are unchanged when old typed identities are weakened and
address maps agree on valid old IDs. Unused entries are unconstrained. -/
theorem sourceBoolRefMemory_wk {D : Source.Layout} {H H' : HTy} (e : H <+: H')
    (address address' : Nat → Nat) (rs : List (HRef H (.array (.prim .bool))))
    (agree : ∀ i,i<H.length → address' i=address i) :
    sourceBoolRefMemory (D := D) address' (rs.map (HRef.wk e))=sourceBoolRefMemory address rs := by
  first
  | solve | rfl | simp only [] | omega
  | apply memory_array_congr (List.length_map (HRef.wk e))
    intro i hi hj
    change (Source.Data.val (.memRef rfl (address' ((rs.map (HRef.wk e))[i]'hi).id)) :
      Source.Data D SourceBoolArrayTy)=.val (.memRef rfl (address (rs[i]'hj).id))
    rw [List.getElem_map]
    change Source.Data.val (.memRef rfl (address' (rs[i]'hj).id))=Source.Data.val (.memRef rfl (address (rs[i]'hj).id))
    rw [agree _ (rs[i]'hj).id_lt]

/-- Preservation derived from old occupied Source cells and native Keeps;
no final observer, Source locals/world equality or global injection is assumed. -/
theorem SourceBoolRefsAt.transport {E : Source.Env} {Γ : Source.RCtx} {H H' : HTy}
    {y z : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {hp' : Heap H'}
    {e : H <+: H'} {r : HRef H BoolRefsRef} {address address' : Nat → Nat}
    (hr : SourceBoolRefsAt y addr hp r address) (keep : Heap.Keeps e hp hp')
    (cells : ∀ a v,y.2.heap.get a=some v → z.2.heap.get a=some v)
    (agree : ∀ i,i<H.length → address' i=address i) :
    SourceBoolRefsAt z addr hp' (r.wk e) address' := by
  first
  | solve | rfl | simp only [] | omega
  | have elems : MObj.elems .dyn (hp'.get (r.wk e))=(MObj.elems .dyn (hp.get r)).map (HRef.wk e) := by
      rw [keep r,MObj.elems_wk];rfl
    refine ⟨?_,?_⟩
    · rw [elems,sourceBoolRefMemory_wk e address address' _ agree]
      exact cells addr _ hr.parent
    · intro q hq
      rw [elems] at hq
      obtain ⟨old,mem,rfl⟩ := List.mem_map.mp hq
      change SourceBoolMemoryAt z (address' old.id) hp' (old.wk e) .dyn
      rw [agree _ old.id_lt]
      exact (hr.children old mem).transport keep cells

/-- Real paired allocation preserves the complete old parent table/children,
freshly extends only the actual new identity, and yields real reached reads. -/
theorem SourceBoolRefsAt.alloc_bool {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H BoolRefsRef} {address : Nat → Nat}
    (hr : SourceBoolRefsAt y addr hp r address) (o : MObj H (.array (.prim .bool)))
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) (F : Source.Fr) :
    let xs := MObj.elems .dyn o
    let z : Source.EMState E Γ := (y.1,{y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory xs⟩).1})
    let pair := hp.alloc o
    let e := List.prefix_append H [RefTy.array (.prim .bool)]
    let address' := allocatedSourceAddress address H.length y.2.heap.next
    (Source.allocRef (E := E) (Γ := Γ) (sourceBoolMemory xs)).run y=(.ok (.memRef rfl y.2.heap.next),z) ∧
    Heap.Keeps e hp pair.1 ∧ SourceBoolRefsAt z addr pair.1 (r.wk e) address' ∧
    SourceBoolMemoryAt z (address' pair.2.id) pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
    pair.2.id=H.length ∧ address' pair.2.id=y.2.heap.next ∧
    (∀ i,i<H.length → address' i=address i) ∧
    (∀ Q (q : HRef H Q),(q.wk e).id≠pair.2.id) ∧ addr≠y.2.heap.next ∧
    (∀ q ∈ MObj.elems .dyn (hp.get r),address q.id≠y.2.heap.next) ∧
    (∀ a v,y.2.heap.get a=some v → z.2.heap.get a=some v) ∧
    (∀ (i j : PrimTy.uint.Denote) (q : HRef H (.array (.prim .bool))) (v : Bool),
      hp.index r .dyn i=some q → hp.index q .dyn j=some v →
      pair.1.index (r.wk e) .dyn i=some (q.wk e) ∧
      (Source.readLoc (E := E) (Γ := Γ) F (τ := SourceBoolArrayTy) (.mem addr i.1.toNat)).run z=
        (.ok (.memRef rfl (address q.id)),z) ∧
      pair.1.index (q.wk e) .dyn j=some v ∧
      (Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem (address q.id) j.1.toNat)).run z=(.ok (.bool v),z)) ∧
    z.1=y.1 ∧ z.2.heap.next=y.2.heap.next+1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧
    z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | rfl | simp only [] | omega
  | dsimp only
    let z : Source.EMState E Γ := (y.1,{y.2 with heap := (y.2.heap.alloc
      ⟨SourceBoolArrayTy,sourceBoolMemory (MObj.elems .dyn o)⟩).1})
    have occupied : ∀ a v,y.2.heap.get a=some v → a≠y.2.heap.next := by
      intro a v found eq
      have empty := y.2.heap.alloc_fresh ⟨SourceBoolArrayTy,sourceBoolMemory (MObj.elems .dyn o)⟩
      change y.2.heap.get y.2.heap.next=none at empty
      rw [←eq,found] at empty;cases empty
    have cells : ∀ a v,y.2.heap.get a=some v → z.2.heap.get a=some v := by
      intro a v found
      exact (Source.Heap.alloc_other y.2.heap _ (occupied a v found)).trans found
    have keep : Heap.Keeps (List.prefix_append H [RefTy.array (.prim .bool)]) hp (hp.alloc o).1 := Heap.keeps_alloc hp o
    have agree := allocatedSourceAddress_old address (H := H) y.2.heap.next
    have parent := hr.transport keep cells agree
    have fresh : SourceBoolMemoryAt z y.2.heap.next (hp.alloc o).1 (hp.alloc o).2 .dyn := by
      unfold SourceBoolMemoryAt
      rw [Heap.get_alloc,MObj.elems_wk,List.map_id'' (f := MVal.wk (List.prefix_append H [RefTy.array (.prim .bool)]) (.prim .bool)) (fun _ => rfl)]
      exact Source.Heap.alloc_get _ _
    have mok := source_bool_alloc_memOK (E := E) (Γ := Γ) SH (MObj.elems .dyn o) y memOK
    rw [source_bool_alloc] at mok
    refine ⟨source_bool_alloc y _,keep,parent,?_,mok.1,rfl,if_pos rfl,agree,?_,occupied _ _ hr.parent,?_,cells,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
    · change SourceBoolMemoryAt z (allocatedSourceAddress address H.length y.2.heap.next H.length) _ _ .dyn
      rw [allocatedSourceAddress,if_pos rfl];exact fresh
    · intro Q q;exact Nat.ne_of_lt q.id_lt
    · intro q mem;exact occupied _ _ (hr.children q mem)
    · intro i j q v hq hv
      change (MObj.elems .dyn (hp.get r))[i.1.toNat]?=some q at hq
      have parentElems : MObj.elems .dyn ((hp.alloc o).1.get (r.wk (List.prefix_append H [RefTy.array (.prim .bool)])))=
          (MObj.elems .dyn (hp.get r)).map (HRef.wk (List.prefix_append H [RefTy.array (.prim .bool)])) := by
        rw [keep r,MObj.elems_wk];rfl
      have hq' : (hp.alloc o).1.index (r.wk (List.prefix_append H [RefTy.array (.prim .bool)])) .dyn i=
          some (q.wk (List.prefix_append H [RefTy.array (.prim .bool)])) := by
        change (MObj.elems .dyn ((hp.alloc o).1.get (r.wk _)))[i.1.toNat]?=_
        rw [parentElems,List.getElem?_map]
        exact congrArg (Option.map (HRef.wk (List.prefix_append H [RefTy.array (.prim .bool)]))) hq
      have hv' : (hp.alloc o).1.index (q.wk (List.prefix_append H [RefTy.array (.prim .bool)])) .dyn j=some v := by
        change (MObj.elems .dyn ((hp.alloc o).1.get (q.wk _)))[j.1.toNat]?=_
        rw [keep q,MObj.elems_wk,List.map_id'' (f := MVal.wk (List.prefix_append H [RefTy.array (.prim .bool)]) (.prim .bool)) (fun _ => rfl)]
        exact hv
      have selected := parent.parent_read F i.1.toNat _ hq'
      have leaf := (parent.child_at i.1.toNat _ hq').read_iff F j v
      change (Source.readLoc (E := E) (Γ := Γ) F (τ := SourceBoolArrayTy) (.mem addr i.1.toNat)).run z=
        (.ok (.memRef rfl (allocatedSourceAddress address H.length y.2.heap.next q.id)),z) at selected
      change ((Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem (allocatedSourceAddress address H.length y.2.heap.next q.id) j.1.toNat)).run z=(.ok (.bool v),z) ↔ _) at leaf
      rw [agree _ q.id_lt] at selected leaf
      exact ⟨hq',selected,hv',leaf.mpr hv'⟩

/-- info: 'Solidity.Backend.MemoryOps.sourceBoolRefMemory_wk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceBoolRefMemory_wk
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.transport
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.alloc_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.alloc_bool
end Solidity.Backend.MemoryOps
