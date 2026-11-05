import Solidity.Backend.MemoryOps.SourceUintSliceNative

/-! Actual slice RHS, local reference binding and reached primitive deletion.
The existing Source and native heaps are composed; emitted allocation, ABI
argument binding and physical memory correspondence remain separate. -/
namespace Solidity.Backend.MemoryOps

def sourceUintSliceBind {E : Source.Env} {Γ : Source.RCtx}
    (dst : Source.Idx Γ SourceUintArrayTy)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish : Source.Idx Γ (.int .u256)) (toEnd : Bool) :
    Source.RExpr E Γ SourceUintArrayTy :=
  .assign (.local dst) (sourceUintSliceCopy root start finish toEnd)

/-- Initial view and operands determine the actual fresh reference stored by
assignment. No final pointer, decoded payload or successful run is a premise. -/
theorem source_uint_slice_bind_native {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (ordered : s.1.toNat≤(if toEnd then len else e.1.toNat))
    (bounded : (if toEnd then len else e.1.toNat)≤len)
    (capacity : (if toEnd then len else e.1.toNat)-s.1.toNat<2^256)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ valid : (CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat)).length<2^256,
      let xs := CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat)
      let pair := hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))
      let mid : Source.EMState E Γ := (y.1.set dst (.memRef rfl y.2.heap.next),
        {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory xs⟩).1})
      (Source.evalE G F (fuel+4) (sourceUintSliceBind dst root start finish toEnd)).run y=
        (.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
      (Source.execS G F (fuel+5) nps none
        (.expr (sourceUintSliceBind dst root start finish toEnd) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal mid.1),(.nil,mid.2)) ∧
      Heap.Keeps (List.prefix_append H [RefTy.array (.prim .uint)]) hp pair.1 ∧
      SourceUintMemoryAt mid y.2.heap.next pair.1 pair.2 .dyn ∧ Source.MemOK E SH mid ∧
      mid.1.get dst=.memRef rfl y.2.heap.next ∧
      (∀ τ (i : Source.Idx Γ τ),dst.toNat≠i.toNat → mid.1.get i=y.1.get i) ∧
      pair.2.id=H.length ∧
      (∀ b obj,y.2.heap.get b=some obj → mid.2.heap.get b=some obj ∧ b≠y.2.heap.next) ∧
      mid.2.ex=y.2.ex ∧ mid.2.events=y.2.events ∧ mid.2.logs=y.2.logs ∧ mid.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | have copy := source_uint_slice_raw_native y hp id G F fuel root start finish off len s e toEnd
      hr hs he ordered bounded capacity SH memOK
    obtain ⟨valid,run,keep,fresh,mok,identity,newAddress,oldMap,separate,preserved,aliases,locals,ex,events,logs,fn⟩ := copy
    rw [newAddress] at fresh
    have boundOK := fresh.bind_memOK dst SH mok
    have bindRun : (Source.evalE G F (fuel+4) (sourceUintSliceBind dst root start finish toEnd)).run y=
        (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1.set dst (.memRef rfl y.2.heap.next),{y.2 with heap := (y.2.heap.alloc
            ⟨SourceUintArrayTy,sourceUintMemory (CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
              ((if toEnd then len else e.1.toNat)-s.1.toNat))⟩).1})) := by
      rw [sourceUintSliceBind,Source.evalE,Source.Hoare.run_bind,run]
      dsimp only
      rw [Source.Hoare.run_bind]
      rfl
    refine ⟨valid,bindRun,source_expr_statement_run G F (fuel+4) nps _ y _ _ bindRun,
      keep,fresh,boundOK,source_locals_get_set _ _ _,?_,identity,preserved,ex,events,logs,fn⟩
    intro τ i ne
    exact source_locals_get_set_other y.1 dst i _ ne

/-- ONE Source Items program binds the computed slice then deletes through
that reached root. Native allocation/write and old occupied cells are derived
from the same execution, without an intermediate representation premise. -/
theorem source_uint_slice_bind_delete {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish index : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e k : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (hi : y.1.get index=sourceUint k)
    (ordered : s.1.toNat≤(if toEnd then len else e.1.toNat))
    (bounded : (if toEnd then len else e.1.toNat)≤len)
    (capacity : (if toEnd then len else e.1.toNat)-s.1.toNat<2^256)
    (bound : k.1.toNat<(if toEnd then len else e.1.toNat)-s.1.toNat)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ valid : (CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat)).length<2^256,
      let xs := CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat)
      let pair := hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))
      let mid : Source.EMState E Γ := (y.1.set dst (.memRef rfl y.2.heap.next),
        {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory xs⟩).1})
      ∃ (out : Heap (H++[RefTy.array (.prim .uint)])) (z : Source.EMState E Γ),
        (Source.evalE G F (fuel+4) (sourceUintSliceBind dst root start finish toEnd)).run y=
          (.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
        (Source.evalE G F (fuel+3) (sourceUintIndexedDelete dst index)).run mid=(.ok Source.RVal.unit,z) ∧
        (Source.execItems G F (fuel+6) nps none
          (.stmt (.expr (sourceUintSliceBind dst root start finish toEnd))
            (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
        pair.1.writeAddr (.index pair.2 .dyn k) (PrimTy.dflt .uint)=some out ∧
        SourceUintMemoryAt z y.2.heap.next out pair.2 .dyn ∧ Source.MemOK E SH z ∧
        Heap.Keeps (List.prefix_append H [RefTy.array (.prim .uint)]) hp out ∧
        MObj.elems .dyn (out.get pair.2)=xs.set k.1.toNat (PrimTy.dflt .uint) ∧
        (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj) ∧
        z.1=mid.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | have binding := source_uint_slice_bind_native y hp G F fuel nps dst root start finish off len s e toEnd
      hr hs he ordered bounded capacity SH memOK
    obtain ⟨valid,first,firstStatement,keep,fresh,mok,selected,other,identity,preserved,ex,events,logs,fn⟩ := binding
    refine ⟨valid,?_⟩
    dsimp only
    let pair := hp.alloc (R := .array (.prim .uint))
      (⟨CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat),valid⟩ : MObj H (.array (.prim .uint)))
    let ext := List.prefix_append H [RefTy.array (.prim .uint)]
    have elements : MObj.elems .dyn (pair.1.get pair.2)=
        CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat) := by
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
      exact List.map_id'' (fun _ => rfl) _
    have inBounds : k.1.toNat<pair.1.len pair.2 .dyn := by
      change k.1.toNat<(MObj.elems .dyn (pair.1.get pair.2)).length
      rw [elements,CalldataPackets.RawUint.payload_length]
      exact bound
    have indexNe : dst.toNat≠index.toNat := by
      intro same
      cases source_idx_type_of_position dst index same
    have indexValue := (other (.int .u256) index indexNe).trans hi
    obtain ⟨out,z,hw,hswrite,new,hmz,values,frames,sourceFrames,locals,exz,eventsz,logsz,fnz⟩ :=
      fresh.write_observed F (fuel+2) k (PrimTy.dflt .uint) inBounds SH mok
    have second := fresh.eval_delete_of_run G F fuel dst index k selected indexValue inBounds hswrite
    have secondStatement := source_expr_statement_run G F (fuel+3) nps _ _ _ _ second
    have keeps : Heap.Keeps ext hp out := by
      intro Q q
      have different : pair.2.id≠(q.wk ext).id := by
        change H.length≠q.id
        exact Ne.symm (Nat.ne_of_lt q.id_lt)
      exact (frames Q (q.wk ext) different).trans (keep q)
    have occupied : ∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj := by
      intro b obj hb
      rw [sourceFrames b (preserved b obj hb).2]
      exact (preserved b obj hb).1
    refine ⟨out,z,first,second,source_items_pair_run G F fuel nps _ _ _ _ _ firstStatement secondStatement,
      hw,new,hmz,keeps,?_,occupied,locals,exz.trans ex,eventsz.trans events,logsz.trans logs,fnz.trans fn⟩
    rw [elements] at values
    exact values

/-- The actual bound reference is retained when the suffix rejects its
index. Items exposes reached globals but erases the local result on error;
no transaction rollback or target post-revert machine is asserted. -/
theorem source_uint_slice_bind_delete_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish index : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e k : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (hi : y.1.get index=sourceUint k)
    (ordered : s.1.toNat≤(if toEnd then len else e.1.toNat))
    (bounded : (if toEnd then len else e.1.toNat)≤len)
    (capacity : (if toEnd then len else e.1.toNat)-s.1.toNat<2^256)
    (bound : (if toEnd then len else e.1.toNat)-s.1.toNat≤k.1.toNat)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ valid : (CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat)).length<2^256,
      let xs := CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat)
      let pair := hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))
      let mid : Source.EMState E Γ := (y.1.set dst (.memRef rfl y.2.heap.next),
        {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory xs⟩).1})
      (Source.evalE G F (fuel+4) (sourceUintSliceBind dst root start finish toEnd)).run y=
        (.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
      (Source.evalE G F (fuel+3) (sourceUintIndexedDelete dst index)).run mid=
        (.error (.revert (Source.panicData .index)),mid) ∧
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintSliceBind dst root start finish toEnd))
          (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
      pair.1.writeAddr (.index pair.2 .dyn k) (PrimTy.dflt .uint)=none ∧
      SourceUintMemoryAt mid y.2.heap.next pair.1 pair.2 .dyn ∧ Source.MemOK E SH mid ∧
      Heap.Keeps (List.prefix_append H [RefTy.array (.prim .uint)]) hp pair.1 ∧
      (∀ b obj,y.2.heap.get b=some obj → mid.2.heap.get b=some obj) := by
  first
  | solve | simp only [] | omega
  | have binding := source_uint_slice_bind_native y hp G F fuel nps dst root start finish off len s e toEnd
      hr hs he ordered bounded capacity SH memOK
    obtain ⟨valid,first,firstStatement,keep,fresh,mok,selected,other,identity,preserved,ex,events,logs,fn⟩ := binding
    refine ⟨valid,?_⟩
    dsimp only
    let pair := hp.alloc (R := .array (.prim .uint))
      (⟨CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat),valid⟩ : MObj H (.array (.prim .uint)))
    have elements : MObj.elems .dyn (pair.1.get pair.2)=
        CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat) := by
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
      exact List.map_id'' (fun _ => rfl) _
    have outside : pair.1.len pair.2 .dyn≤k.1.toNat := by
      change (MObj.elems .dyn (pair.1.get pair.2)).length≤k.1.toNat
      rw [elements,CalldataPackets.RawUint.payload_length]
      exact bound
    have indexNe : dst.toNat≠index.toNat := by
      intro same
      cases source_idx_type_of_position dst index same
    have indexValue := (other (.int .u256) index indexNe).trans hi
    let mid : Source.EMState E Γ := (y.1.set dst (.memRef rfl y.2.heap.next),
      {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory
        (CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat))⟩).1})
    have second : (Source.evalE G F (fuel+3) (sourceUintIndexedDelete dst index)).run mid=
        (.error (.revert (Source.panicData .index)),mid) := by
      rw [sourceUintIndexedDelete,Source.evalE,Source.Hoare.run_bind,
        fresh.eval_index_bounds G F fuel dst index k selected indexValue outside]
    have secondStatement := source_expr_statement_error G F (fuel+3) nps _ _ _ _ second
    refine ⟨first,second,source_items_pair_error G F fuel nps _ _ _ _ _ _ firstStatement secondStatement,
      (fresh.delete_bounds F fuel k outside).2,fresh,mok,keep,?_⟩
    intro b obj hb
    exact (preserved b obj hb).1

/-- info: 'Solidity.Backend.MemoryOps.source_uint_slice_bind_delete_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_slice_bind_delete_bounds

/-- info: 'Solidity.Backend.MemoryOps.source_uint_slice_bind_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_slice_bind_native
/-- info: 'Solidity.Backend.MemoryOps.source_uint_slice_bind_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_slice_bind_delete
end Solidity.Backend.MemoryOps
