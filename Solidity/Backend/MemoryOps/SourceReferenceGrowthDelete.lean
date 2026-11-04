import Solidity.Backend.MemoryOps.SourceReferenceGrowthWrite

/-! Deletion through a genuinely fresh redirected child. Actual allocation
freshness discharges the selected-footprint separation condition; no global
address injection or reached-state oracle is introduced. Operation-side only:
no Source allocation expression or emitted allocator/word postimage is claimed. -/
namespace Solidity.Backend.MemoryOps

/-- An old occupied Source child cannot have the next allocation address.
This separates every retained child from the actual fresh redirect target. -/
theorem SourceBoolRefsAt.fresh_redirect_separated {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y addr hp r address)
    (o : MObj H (.array (.prim .bool))) (i : Nat) :
    let e := List.prefix_append H [RefTy.array (.prim .bool)]
    let address' := allocatedSourceAddress address H.length y.2.heap.next
    ∀ t∈((MObj.elems .dyn (hp.get r)).map (HRef.wk e)).set i (hp.alloc o).2,
      t.id≠(hp.alloc o).2.id → address' t.id≠address' (hp.alloc o).2.id := by
  first
  | solve | rfl | simp only [] | omega
  | dsimp only
    intro t member different
    rcases List.mem_or_eq_of_mem_set member with old | same
    · obtain ⟨q,mem,rfl⟩ := List.mem_map.mp old
      change allocatedSourceAddress address H.length y.2.heap.next q.id≠
        allocatedSourceAddress address H.length y.2.heap.next (hp.alloc o).2.id
      have freshId : (hp.alloc o).2.id=H.length := rfl
      rw [allocatedSourceAddress_old address _ _ q.id_lt,freshId]
      simp only [allocatedSourceAddress,if_pos rfl]
      change address q.id≠y.2.heap.next
      intro equal
      have occupied := hr.children q mem
      have absent := y.2.heap.alloc_fresh ⟨SourceBoolArrayTy,sourceBoolMemory (MObj.elems .dyn o)⟩
      change y.2.heap.get y.2.heap.next=none at absent
      rw [←equal,occupied] at absent
      cases absent
    · exact False.elim (different (congrArg HRef.id same))

/-- Real allocation and pointer redirection feed the actual nested Source delete.
The selected object, capacity, local alignment, MemOK and alias separation are
all derived from the initial observer and actual preceding outputs. -/
theorem SourceBoolRefsAt.alloc_redirect_delete {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y addr hp r address)
    (o : MObj H (.array (.prim .bool))) (SH : Source.HeapTy) (hm : Source.MemOK E SH y)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (pi pj : Source.Idx Γ (.int .u256))
    (i : Fin Evm.W) (j : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl addr) (hpi : y.1.get pi=sourceUint (Evm.Memory.indexValue i))
    (hpj : y.1.get pj=sourceUint j) (hi : i.val<hp.len r .dyn)
    (hj : j.1.toNat<(MObj.elems .dyn o).length) :
    let pair := hp.alloc o
    let e := List.prefix_append H [RefTy.array (.prim .bool)]
    let address' := allocatedSourceAddress address H.length y.2.heap.next
    let allocated : Source.EMState E Γ := (y.1,{y.2 with heap :=
      (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (MObj.elems .dyn o)⟩).1})
    ∃ (mid out : Heap (H++[RefTy.array (.prim .bool)])) (z w : Source.EMState E Γ),
      (Source.allocRef (E := E) (Γ := Γ) (sourceBoolMemory (MObj.elems .dyn o))).run y=
        (.ok (.memRef rfl y.2.heap.next),allocated) ∧
      pair.1.writeAddr (.index (r.wk e) .dyn (Evm.Memory.indexValue i)) pair.2=some mid ∧
      (Source.writeLoc (E := E) (Γ := Γ) F (horizon+4) (.mem (τ := SourceBoolArrayTy) addr i.val)
        (.memRef rfl (address' pair.2.id))).run allocated=(.ok (),z) ∧
      mid.index (r.wk e) .dyn (Evm.Memory.indexValue i)=some pair.2 ∧
      mid.writeAddr (.index pair.2 .dyn j) false=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F (horizon+3) (.mem (address' pair.2.id) j.1.toNat) (.bool false)).run z=(.ok (),w) ∧
      (Source.evalE G F (horizon+4) (sourceNestedDelete root pi pj)).run z=(.ok Source.RVal.unit,w) ∧
      SourceBoolRefsAt z addr mid (r.wk e) address' ∧
      SourceBoolRefsAt w addr out (r.wk e) address' ∧
      Source.MemOK E SH z ∧ Source.MemOK E SH w ∧ z.1=y.1 ∧ w.1=y.1 ∧
      out.get (r.wk e)=mid.get (r.wk e) ∧
      MObj.elems .dyn (mid.get pair.2)=MObj.elems .dyn o ∧
      (∀ t∈MObj.elems .dyn (mid.get (r.wk e)),t.id≠pair.2.id → address' t.id≠address' pair.2.id) ∧
      (∀ q : HRef H (.array (.prim .bool)),out.get (q.wk e)=MObj.wk e _ (hp.get q)) ∧
      MObj.elems .dyn (out.get pair.2)=(MObj.elems .dyn o).set j.1.toNat false ∧
      (∀ a,a≠address' pair.2.id → w.2.heap.get a=z.2.heap.get a) ∧
      w.2.heap.next=z.2.heap.next ∧
      (w.2.ex=y.2.ex ∧ w.2.events=y.2.events ∧ w.2.logs=y.2.logs ∧ w.2.fnLocals=y.2.fnLocals) := by
  first
  | solve | rfl | simp only [] | omega
  | dsimp only
    obtain ⟨mid,z,ha,hw,hs,initial,parent,fresh,ma,mz,lz,rs,raw,old,aliases,hid,haddr,distinct,world,cells,next⟩ :=
      hr.alloc_redirect o SH hm F (horizon+4) i hi
    have selected : mid.index (r.wk (List.prefix_append H [RefTy.array (.prim .bool)])) .dyn
        (Evm.Memory.indexValue i)=some (hp.alloc o).2 := Heap.readAddr_writeAddr_same hw
    have member : (hp.alloc o).2∈MObj.elems .dyn (mid.get (r.wk (List.prefix_append H [RefTy.array (.prim .bool)]))) := List.mem_of_getElem? selected
    have separate : ∀ t∈MObj.elems .dyn (mid.get (r.wk (List.prefix_append H [RefTy.array (.prim .bool)]))),t.id≠(hp.alloc o).2.id →
        allocatedSourceAddress address H.length y.2.heap.next t.id≠
          allocatedSourceAddress address H.length y.2.heap.next (hp.alloc o).2.id := by
      rw [rs]
      exact hr.fresh_redirect_separated o i.val
    have elems : MObj.elems .dyn (mid.get (hp.alloc o).2)=MObj.elems .dyn o := by
      rw [raw,Heap.get_alloc,MObj.elems_wk,List.map_id'' (f := MVal.wk (List.prefix_append H [RefTy.array (.prim .bool)]) (.prim .bool)) (fun _ => rfl)]
    have bounds : j.1.toNat<mid.len (hp.alloc o).2 .dyn := by
      change j.1.toNat<(MObj.elems .dyn (mid.get (hp.alloc o).2)).length
      rw [elems];exact hj
    obtain ⟨out,w,hwrite,sw,post,mw,lw,keepParent⟩ := parent.write_child (hp.alloc o).2 member separate F (horizon+3) j false bounds SH mz
    have run := parent.eval_nested_delete_of_write G F horizon root pi pj (Evm.Memory.indexValue i) j (hp.alloc o).2
      (by rw [lz];exact hroot) (by rw [lz];exact hpi) (by rw [lz];exact hpj) selected bounds sw
    simp only [Heap.len] at bounds
    have canonical : out=mid.set (hp.alloc o).2 (MObj.setElem .dyn (mid.get (hp.alloc o).2) j.1.toNat false) := by
      simpa only [Heap.writeAddr,Heap.setIndex,bounds,↓reduceIte,Option.some.injEq] using hwrite.symm
    obtain ⟨ht,sourceWrite⟩ := source_bool_write z _ _ (parent.children (hp.alloc o).2 member) j.1.toNat bounds false
    have same := congrArg Prod.snd (sw.symm.trans sourceWrite)
    dsimp only at same
    refine ⟨mid,out,z,w,ha,hw,hs,selected,hwrite,sw,run,parent,post,mz,mw,lz,lw.trans lz,keepParent,elems,separate,?_,?_,?_,?_,?_⟩
    · intro q
      rw [canonical,Heap.get_set_ne mid (hp.alloc o).2 (q.wk _) (Ne.symm (distinct _ q))]
      exact old q
    · rw [canonical,Heap.get_set_same,MObj.elems_setElem,elems]
    · intro a hne
      rw [same]
      exact Source.Heap.write_other _ hne _ ht
    · rw [same];rfl
    · rw [same]
      exact world

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.fresh_redirect_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.fresh_redirect_separated
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.alloc_redirect_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.alloc_redirect_delete
end Solidity.Backend.MemoryOps
