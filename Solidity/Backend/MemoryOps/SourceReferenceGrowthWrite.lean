import Solidity.Backend.MemoryOps.SourceReferenceGrowth
import Solidity.Backend.MemoryOps.SourceReferenceWrite

/-! Actual paired allocation followed by redirection of one existing parent
slot to the fresh Boolean child. No Source new-expression, emitted allocator,
word postimage or recursive constructor is supplied by this operation adapter. -/
namespace Solidity.Backend.MemoryOps

/-- All second-stage representation, bounds and MemOK premises come from the
actual first allocation. The old Boolean children and fresh payload survive
pointer replacement, including repeated old aliases. -/
theorem SourceBoolRefsAt.alloc_redirect {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y addr hp r address)
    (o : MObj H (.array (.prim .bool))) (SH : Source.HeapTy) (hm : Source.MemOK E SH y)
    (F : Source.Fr) (fuel : Nat) (i : Fin Evm.W) (hi : i.val<hp.len r .dyn) :
    let pair := hp.alloc o
    let e := List.prefix_append H [RefTy.array (.prim .bool)]
    let address' := allocatedSourceAddress address H.length y.2.heap.next
    let mid : Source.EMState E Γ := (y.1,{y.2 with heap :=
      (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (MObj.elems .dyn o)⟩).1})
    ∃ (out : Heap (H++[RefTy.array (.prim .bool)])) (z : Source.EMState E Γ),
      (Source.allocRef (E := E) (Γ := Γ) (sourceBoolMemory (MObj.elems .dyn o))).run y=
        (.ok (.memRef rfl y.2.heap.next),mid) ∧
      pair.1.writeAddr (.index (r.wk e) .dyn (Evm.Memory.indexValue i)) pair.2=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (τ := SourceBoolArrayTy) addr i.val)
        (.memRef rfl (address' pair.2.id))).run mid=(.ok (),z) ∧
      SourceBoolRefsAt mid addr pair.1 (r.wk e) address' ∧
      SourceBoolRefsAt z addr out (r.wk e) address' ∧
      SourceBoolMemoryAt z (address' pair.2.id) out pair.2 .dyn ∧
      Source.MemOK E SH mid ∧ Source.MemOK E SH z ∧ z.1=y.1 ∧
      MObj.elems .dyn (out.get (r.wk e))=
        ((MObj.elems .dyn (hp.get r)).map (HRef.wk e)).set i.val pair.2 ∧
      out.get pair.2=pair.1.get pair.2 ∧
      (∀ q : HRef H (.array (.prim .bool)),out.get (q.wk e)=MObj.wk e _ (hp.get q)) ∧
      (∀ q : HRef H (.array (.prim .bool)),SourceBoolMemoryAt y (address q.id) hp q .dyn →
        SourceBoolMemoryAt z (address q.id) out (q.wk e) .dyn) ∧
      pair.2.id=H.length ∧ address' pair.2.id=y.2.heap.next ∧
      (∀ Q (q : HRef H Q),(q.wk e).id≠pair.2.id) ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) ∧
      (∀ a,a≠addr → z.2.heap.get a=mid.2.heap.get a) ∧ z.2.heap.next=mid.2.heap.next := by
  first
  | solve | rfl | simp only [] | omega
  | dsimp only
    obtain ⟨ha,keep,parent,fresh,mem,hid,haddr,agree,distinct,hparent,hchildren,cells,reads,locals,tail⟩ :=
      hr.alloc_bool o SH hm F
    have bounds : i.val<(hp.alloc o).1.len (r.wk (List.prefix_append H [RefTy.array (.prim .bool)])) .dyn := by
      rw [Heap.Keeps.len keep];exact hi
    obtain ⟨out,z,hw,hs,post,mz,lz,rs,children,frames,world⟩ :=
      parent.write_reference (hp.alloc o).2 fresh F fuel i bounds SH mem
    refine ⟨out,z,ha,hw,hs,parent,post,frames _ fresh,mem,mz,lz.trans locals,?_,children _,?_,?_,hid,haddr,distinct,world,?_,?_⟩
    · rw [rs,keep r,MObj.elems_wk];rfl
    · intro q
      exact (children (q.wk _)).trans (keep q)
    · intro q hq
      have prior := hq.transport keep cells
      have reached := frames (q.wk (List.prefix_append H [RefTy.array (.prim .bool)])) (by
        change SourceBoolMemoryAt _ ((allocatedSourceAddress address H.length y.2.heap.next) q.id) _ _ .dyn
        rw [agree _ q.id_lt]
        exact prior)
      change SourceBoolMemoryAt z
        ((allocatedSourceAddress address H.length y.2.heap.next) q.id) out (q.wk _) .dyn at reached
      rw [agree _ q.id_lt] at reached
      exact reached
    · obtain ⟨ht,hset⟩ := source_refs_write _ addr _ _ parent.parent i.val bounds (hp.alloc o).2
      have same := congrArg Prod.snd (hs.symm.trans hset)
      dsimp only at same
      intro a hne
      rw [same]
      exact Source.Heap.write_other _ hne _ ht
    · obtain ⟨ht,hset⟩ := source_refs_write _ addr _ _ parent.parent i.val bounds (hp.alloc o).2
      have same := congrArg Prod.snd (hs.symm.trans hset)
      dsimp only at same
      rw [same]
      rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.alloc_redirect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolRefsAt.alloc_redirect
end Solidity.Backend.MemoryOps
