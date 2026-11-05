import Solidity.Backend.MemoryOps.SourceUintSliceBinding
import Solidity.Backend.MemoryOps.SourceUintCompound

/-! Arithmetic through the actual newly bound slice. Existing arithmetic,
write/frame and Items producers are composed, without a decoded old-value
oracle or an emitted fresh-payload allocator claim. -/
namespace Solidity.Backend.MemoryOps

/-- Existing compound execution exposes its actual write, so ordinary write
preservation yields the full observer/MemOK and world/heap frame certificate. -/
theorem SourceUintMemoryAt.compound_add_observed {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ SourceUintArrayTy) (index rhs : Source.Idx Γ (.int .u256))
    (k value : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hi : y.1.get index=sourceUint k) (hv : y.1.get rhs=sourceUint value)
    (bound : k.1.toNat<hp.len r a)
    (add : PrimTy.uint.inRange ((MObj.elems a (hp.get r))[k.1.toNat].1+value.1)=true)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    let sum : PrimTy.uint.Denote := ⟨(MObj.elems a (hp.get r))[k.1.toNat].1+value.1,add⟩
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r a k) sum=some out ∧
      (Source.evalE G F (fuel+3) (sourceUintIndexedAdd root index rhs)).run y=(.ok (.val (sourceUint sum)),z) ∧
      SourceUintMemoryAt z address out r a ∧ Source.MemOK E SH z ∧
      MObj.elems a (out.get r)=(MObj.elems a (hp.get r)).set k.1.toNat sum ∧
      (∀ Q (q : HRef H Q),r.id≠q.id → out.get q=hp.get q) ∧
      (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
      z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨out,z,write,sourceWrite,run,new,locals⟩ := hr.compound_add G F fuel root index rhs k value hroot hi hv bound add
    obtain ⟨_,frames,sourceFrames,aliases,ex,events,logs,fn⟩ := hr.write_frames F (fuel+2) k _ bound write sourceWrite
    have mok := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F (fuel+2)
      (.mem (τ := .int .u256) address k.1.toNat)
      (sourceUint ⟨(MObj.elems a (hp.get r))[k.1.toNat].1+value.1,add⟩) y ⟨memOK,Source.Val.refOK_of_loc rfl _⟩
    rw [sourceWrite] at mok
    refine ⟨out,z,write,run,new,mok,indexedWrite_elems hp out r a k _ write,?_,sourceFrames,locals,ex,events,logs,fn⟩
    intro Q q ne
    exact frames q ne

/-- The initial byte payload determines the old cell, and the actual binding
output supplies both scalar alignment and the fresh representation consumed
by addition. A single Items execution links both statements. -/
theorem source_uint_slice_bind_add {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish index rhs : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e k value : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (hi : y.1.get index=sourceUint k) (hv : y.1.get rhs=sourceUint value)
    (ordered : s.1.toNat≤(if toEnd then len else e.1.toNat))
    (bounded : (if toEnd then len else e.1.toNat)≤len)
    (capacity : (if toEnd then len else e.1.toNat)-s.1.toNat<2^256)
    (bound : k.1.toNat<(if toEnd then len else e.1.toNat)-s.1.toNat)
    (add : PrimTy.uint.inRange (((CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
      ((if toEnd then len else e.1.toNat)-s.1.toNat))[k.1.toNat]?.getD (PrimTy.dflt .uint)).1+value.1)=true)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ valid : (CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat)).length<2^256,
      let xs := CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)
      let sum : PrimTy.uint.Denote := ⟨(xs[k.1.toNat]?.getD (PrimTy.dflt .uint)).1+value.1,add⟩
      let pair := hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))
      let mid : Source.EMState E Γ := (y.1.set dst (.memRef rfl y.2.heap.next),
        {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory xs⟩).1})
      ∃ (out : Heap (H++[RefTy.array (.prim .uint)])) (z : Source.EMState E Γ),
        (Source.evalE G F (fuel+4) (sourceUintSliceBind dst root start finish toEnd)).run y=
          (.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
        (Source.evalE G F (fuel+3) (sourceUintIndexedAdd dst index rhs)).run mid=(.ok (.val (sourceUint sum)),z) ∧
        (Source.execItems G F (fuel+6) nps none
          (.stmt (.expr (sourceUintSliceBind dst root start finish toEnd))
            (.stmt (.expr (sourceUintIndexedAdd dst index rhs)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
        pair.1.writeAddr (.index pair.2 .dyn k) sum=some out ∧
        SourceUintMemoryAt z y.2.heap.next out pair.2 .dyn ∧ Source.MemOK E SH z ∧
        Heap.Keeps (List.prefix_append H [RefTy.array (.prim .uint)]) hp out ∧
        MObj.elems .dyn (out.get pair.2)=xs.set k.1.toNat sum ∧
        (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj) ∧
        (∀ b,b≠y.2.heap.next → z.2.heap.get b=mid.2.heap.get b) ∧
        z.1=mid.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | have binding := source_uint_slice_bind_native y hp G F fuel nps dst root start finish off len s e toEnd
      hr hs he ordered bounded capacity SH memOK
    obtain ⟨valid,first,firstStatement,keep,fresh,mok,selected,other,identity,preserved,ex,events,logs,fn⟩ := binding
    refine ⟨valid,?_⟩
    dsimp only
    let xs := CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)
    let pair := hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))
    let ext := List.prefix_append H [RefTy.array (.prim .uint)]
    have elements : MObj.elems .dyn (pair.1.get pair.2)=xs := by
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
      exact List.map_id'' (fun _ => rfl) _
    have inBounds : k.1.toNat<pair.1.len pair.2 .dyn := by
      change k.1.toNat<(MObj.elems .dyn (pair.1.get pair.2)).length
      rw [elements,CalldataPackets.RawUint.payload_length]
      exact bound
    have selectedValue : xs[k.1.toNat]?.getD (PrimTy.dflt .uint)=
        (MObj.elems .dyn (pair.1.get pair.2))[k.1.toNat]'inBounds := by
      have hget : xs[k.1.toNat]?=some ((MObj.elems .dyn (pair.1.get pair.2))[k.1.toNat]'inBounds) :=
        (congrArg (fun vs => vs[k.1.toNat]?) elements).symm.trans (List.getElem?_eq_getElem inBounds)
      exact congrArg (fun v => v.getD (PrimTy.dflt .uint)) hget
    have arithmetic : PrimTy.uint.inRange ((MObj.elems .dyn (pair.1.get pair.2))[k.1.toNat].1+value.1)=true := by
      rw [←selectedValue]
      exact add
    have scalarNe : ∀ (i : Source.Idx Γ (.int .u256)),dst.toNat≠i.toNat := by
      intro i same
      cases source_idx_type_of_position dst i same
    have run := fresh.compound_add_observed G F fuel dst index rhs k value selected
      ((other _ index (scalarNe index)).trans hi) ((other _ rhs (scalarNe rhs)).trans hv) inBounds arithmetic SH mok
    have sumEq : (⟨(MObj.elems .dyn (pair.1.get pair.2))[k.1.toNat].1+value.1,arithmetic⟩ : PrimTy.uint.Denote)=
        ⟨(xs[k.1.toNat]?.getD (PrimTy.dflt .uint)).1+value.1,add⟩ := by
      apply Subtype.ext
      exact congrArg (fun v : PrimTy.uint.Denote => v.1+value.1) selectedValue.symm
    rw [sumEq] at run
    obtain ⟨out,z,write,second,new,hmz,values,frames,sourceFrames,locals,exz,eventsz,logsz,fnz⟩ := run
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
    refine ⟨out,z,first,second,source_items_pair_run G F fuel nps _ _ _ _ _ firstStatement
      (source_expr_statement_run G F (fuel+3) nps _ _ _ _ second),write,new,hmz,keeps,?_,occupied,sourceFrames,locals,
      exz.trans ex,eventsz.trans events,logsz.trans logs,fnz.trans fn⟩
    rw [elements] at values
    exact values

/-- Checked overflow observes the fresh slice, not the old destination.
The successful binding prefix is retained in Source globals; no suffix write,
rollback, panic-byte equality or target error machine is invented. -/
theorem source_uint_slice_bind_add_overflow {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish index rhs : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e k value : PrimTy.uint.Denote) (toEnd : Bool) (checked : F.checked=true)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (hi : y.1.get index=sourceUint k) (hv : y.1.get rhs=sourceUint value)
    (ordered : s.1.toNat≤(if toEnd then len else e.1.toNat))
    (bounded : (if toEnd then len else e.1.toNat)≤len)
    (capacity : (if toEnd then len else e.1.toNat)-s.1.toNat<2^256)
    (bound : k.1.toNat<(if toEnd then len else e.1.toNat)-s.1.toNat)
    (bad : PrimTy.uint.inRange (((CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
      ((if toEnd then len else e.1.toNat)-s.1.toNat))[k.1.toNat]?.getD (PrimTy.dflt .uint)).1+value.1)≠true)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ valid : (CalldataPackets.RawUint.payload F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat)).length<2^256,
      let xs := CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)
      let pair := hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))
      let mid : Source.EMState E Γ := (y.1.set dst (.memRef rfl y.2.heap.next),
        {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory xs⟩).1})
      (Source.evalE G F (fuel+4) (sourceUintSliceBind dst root start finish toEnd)).run y=
        (.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
      (Source.evalE G F (fuel+3) (sourceUintIndexedAdd dst index rhs)).run mid=
        (.error (.revert (Source.panicData .arithmetic)),mid) ∧
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintSliceBind dst root start finish toEnd))
          (.stmt (.expr (sourceUintIndexedAdd dst index rhs)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,mid.2)) ∧
      compoundT .add .uint (xs[k.1.toNat]?.getD (PrimTy.dflt .uint)).1 value.1=none ∧
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
    let xs := CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)
    let pair := hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))
    have elements : MObj.elems .dyn (pair.1.get pair.2)=xs := by
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
      exact List.map_id'' (fun _ => rfl) _
    have inBounds : k.1.toNat<pair.1.len pair.2 .dyn := by
      change k.1.toNat<(MObj.elems .dyn (pair.1.get pair.2)).length
      rw [elements,CalldataPackets.RawUint.payload_length]
      exact bound
    have selectedValue : xs[k.1.toNat]?.getD (PrimTy.dflt .uint)=
        (MObj.elems .dyn (pair.1.get pair.2))[k.1.toNat]'inBounds := by
      have hget : xs[k.1.toNat]?=some ((MObj.elems .dyn (pair.1.get pair.2))[k.1.toNat]'inBounds) :=
        (congrArg (fun vs => vs[k.1.toNat]?) elements).symm.trans (List.getElem?_eq_getElem inBounds)
      exact congrArg (fun v => v.getD (PrimTy.dflt .uint)) hget
    have arithmetic : PrimTy.uint.inRange ((MObj.elems .dyn (pair.1.get pair.2))[k.1.toNat].1+value.1)≠true := by
      rw [←selectedValue]
      exact bad
    have scalarNe : ∀ (i : Source.Idx Γ (.int .u256)),dst.toNat≠i.toNat := by
      intro i same
      cases source_idx_type_of_position dst i same
    have second := fresh.compound_add_overflow G F fuel checked dst index rhs k value selected
      ((other _ index (scalarNe index)).trans hi) ((other _ rhs (scalarNe rhs)).trans hv) inBounds arithmetic
    refine ⟨first,second,source_items_pair_error G F fuel nps _ _ _ _ _ _ firstStatement
      (source_expr_statement_error G F (fuel+3) nps _ _ _ _ second),
      (source_uint_add_overflow (D := E.layout) (xs[k.1.toNat]?.getD (PrimTy.dflt .uint)) value bad).2,fresh,mok,keep,?_⟩
    intro b obj hb
    exact (preserved b obj hb).1

/-- info: 'Solidity.Backend.MemoryOps.source_uint_slice_bind_add_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_slice_bind_add_overflow

/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.compound_add_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.compound_add_observed
/-- info: 'Solidity.Backend.MemoryOps.source_uint_slice_bind_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_slice_bind_add
end Solidity.Backend.MemoryOps
