import Solidity.Backend.MemoryOps.SourceUintSliceCompound

/-! Actual changed-cell read after slice binding and arithmetic. Existing
Source Items, read and local assignment semantics are reused. Native heap
operations are linked; emitted payload allocation remains a separate producer. -/
namespace Solidity.Backend.MemoryOps

/-- Existing Items consumes each reached statement output. The last error
exposes reached globals, with no invented returned local environment. -/
theorem source_items_triple_error {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (s t u : Source.RStmt E [] false .body Γ Γ) (y mid changed failed : Source.EMState E Γ)
    (halt : Source.Halt)
    (first : (Source.execS G F (n+3) nps none s y.1).run (.nil,y.2)=(.ok (.normal mid.1),(.nil,mid.2)))
    (second : (Source.execS G F (n+2) nps none t mid.1).run (.nil,mid.2)=(.ok (.normal changed.1),(.nil,changed.2)))
    (third : (Source.execS G F (n+1) nps none u changed.1).run (.nil,changed.2)=(.error halt,(.nil,failed.2))) :
    (Source.execItems G F (n+4) nps none (.stmt s (.stmt t (.stmt u .nil))) y.1).run (.nil,y.2)=
      (.error halt,(.nil,failed.2)) := by
  first
  | solve | simp only [] | omega
  | rw [Source.execItems,Source.Hoare.run_bind,first]
    change (Source.execItems G F (n+3) nps none (.stmt t (.stmt u .nil)) mid.1 >>=
      fun o => Source.EM.lift (o.up Γ)).run (.nil,mid.2)=_
    rw [Source.Hoare.run_bind]
    have tail : (Source.execItems G F (n+3) nps none (.stmt t (.stmt u .nil)) mid.1).run (.nil,mid.2)=
        (.error halt,(.nil,failed.2)) := by
      rw [Source.execItems,Source.Hoare.run_bind,second]
      change (Source.execItems G F (n+2) nps none (.stmt u .nil) changed.1 >>=
        fun o => Source.EM.lift (o.up Γ)).run (.nil,changed.2)=_
      rw [Source.Hoare.run_bind]
      have last : (Source.execItems G F (n+2) nps none (.stmt u .nil) changed.1).run (.nil,changed.2)=
          (.error halt,(.nil,failed.2)) := by
        rw [Source.execItems,Source.Hoare.run_bind,third]
      rw [last]
    rw [tail]

/-- Initial bytes/operands derive allocation, update and the read of the
actually changed cell. The result local may equal the index or RHS local;
its overwrite happens after that read, not before it. -/
theorem source_uint_slice_bind_add_read {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (root : Source.Idx Γ (.array .calldata (.int .u256) none))
    (start finish index rhs result : Source.Idx Γ (.int .u256)) (off len : Nat)
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
      ∃ (out : Heap (H++[RefTy.array (.prim .uint)])) (changed : Source.EMState E Γ),
        let final : Source.EMState E Γ := (changed.1.set result (sourceUint sum),changed.2)
        (Source.evalE G F (fuel+5) (sourceUintSliceBind dst root start finish toEnd)).run y=
          (.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
        (Source.evalE G F (fuel+4) (sourceUintIndexedAdd dst index rhs)).run mid=(.ok (.val (sourceUint sum)),changed) ∧
        (Source.evalE G F (fuel+2) (.indexArray (.local dst) (.local index) rfl)).run changed=
          (.ok (.val (sourceUint sum)),changed) ∧
        (Source.evalE G F (fuel+3) (sourceUintReadInto dst index result)).run changed=(.ok (.val (sourceUint sum)),final) ∧
        (Source.execItems G F (fuel+7) nps none
          (.stmt (.expr (sourceUintSliceBind dst root start finish toEnd))
            (.stmt (.expr (sourceUintIndexedAdd dst index rhs)) (.stmt (.expr (sourceUintReadInto dst index result)) .nil)) :
              Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal final.1),(.nil,final.2)) ∧
        pair.1.writeAddr (.index pair.2 .dyn k) sum=some out ∧
        (MObj.elems .dyn (out.get pair.2))[k.1.toNat]?=some sum ∧
        SourceUintMemoryAt final y.2.heap.next out pair.2 .dyn ∧ Source.MemOK E SH final ∧
        Heap.Keeps (List.prefix_append H [RefTy.array (.prim .uint)]) hp out ∧
        MObj.elems .dyn (out.get pair.2)=xs.set k.1.toNat sum ∧
        final.1.get dst=.memRef rfl y.2.heap.next ∧ final.1.get result=sourceUint sum ∧
        (∀ τ (i : Source.Idx Γ τ),dst.toNat≠i.toNat → result.toNat≠i.toNat → final.1.get i=y.1.get i) ∧
        (∀ b obj,y.2.heap.get b=some obj → final.2.heap.get b=some obj) ∧
        (∀ b,b≠y.2.heap.next → final.2.heap.get b=mid.2.heap.get b) ∧
        changed.1=mid.1 ∧ final.2.ex=y.2.ex ∧ final.2.events=y.2.events ∧
        final.2.logs=y.2.logs ∧ final.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | have program := source_uint_slice_bind_add y hp G F (fuel+1) nps dst root start finish index rhs off len s e k value toEnd
      hr hs he hi hv ordered bounded capacity bound add SH memOK
    obtain ⟨valid,out,changed,first,second,prefixRun,write,new,mok,keep,values,occupied,sourceFrames,locals,ex,events,logs,fn⟩ := program
    refine ⟨valid,out,changed,?_⟩
    dsimp only
    let xs := CalldataPackets.RawUint.payload F (off+32*s.1.toNat) ((if toEnd then len else e.1.toNat)-s.1.toNat)
    let sum : PrimTy.uint.Denote := ⟨(xs[k.1.toNat]?.getD (PrimTy.dflt .uint)).1+value.1,add⟩
    let pair := hp.alloc (R := .array (.prim .uint)) (⟨xs,valid⟩ : MObj H (.array (.prim .uint)))
    let mid : Source.EMState E Γ := (y.1.set dst (.memRef rfl y.2.heap.next),
      {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory xs⟩).1})
    let final : Source.EMState E Γ := (changed.1.set result (sourceUint sum),changed.2)
    have oldBound : k.1.toNat<xs.length := by rw [CalldataPackets.RawUint.payload_length];exact bound
    have inBounds : k.1.toNat<out.len pair.2 .dyn := by
      change k.1.toNat<(MObj.elems .dyn (out.get pair.2)).length
      rw [values,List.length_set]
      exact oldBound
    have readValue : (MObj.elems .dyn (out.get pair.2))[k.1.toNat]?=some sum := by
      rw [values]
      exact List.getElem?_set_self oldBound
    have nativeValue : (MObj.elems .dyn (out.get pair.2))[k.1.toNat]'inBounds=sum :=
      Option.some.inj ((List.getElem?_eq_getElem inBounds).symm.trans readValue)
    have rootValue : changed.1.get dst=.memRef rfl y.2.heap.next := by
      rw [locals]
      exact source_locals_get_set _ _ _
    have scalarNe : dst.toNat≠index.toNat := by
      intro same
      cases source_idx_type_of_position dst index same
    have indexValue : changed.1.get index=sourceUint k := by
      rw [locals]
      exact (source_locals_get_set_other y.1 dst index _ scalarNe).trans hi
    have read := new.eval_index G F fuel dst index k rootValue indexValue inBounds
    rw [nativeValue] at read
    have third := source_uint_read_into_of_run G F fuel changed dst index result sum read
    have firstRun : (Source.evalE G F (fuel+5) (sourceUintSliceBind dst root start finish toEnd)).run y=
        (.ok (.val (.memRef rfl y.2.heap.next)),mid) := by simpa only [Nat.add_assoc] using first
    have secondRun : (Source.evalE G F (fuel+4) (sourceUintIndexedAdd dst index rhs)).run mid=
        (.ok (.val (sourceUint sum)),changed) := by simpa only [Nat.add_assoc] using second
    have tail := source_items_pair_run G F fuel nps _ _ mid changed final
      (source_expr_statement_run G F (fuel+4) nps _ mid changed _ secondRun)
      (source_expr_statement_run G F (fuel+3) nps _ changed final _ third)
    have items := source_items_cons_run G F (fuel+6) nps _ _ y mid final
      (source_expr_statement_run G F (fuel+5) nps _ y mid _ firstRun) tail
    have finalOK : Source.MemOK E SH final :=
      ⟨⟨mok.1.1,Source.LocalsOK.set changed.1 result mok.1.2 (Source.Val.refOK_of_loc rfl _)⟩,mok.2⟩
    have resultNe : result.toNat≠dst.toNat := by
      intro same
      cases source_idx_type_of_position result dst same
    refine ⟨firstRun,secondRun,read,third,items,write,readValue,new,finalOK,keep,values,
      (source_locals_get_set_other changed.1 result dst _ resultNe).trans rootValue,
      source_locals_get_set _ _ _,?_,occupied,sourceFrames,locals,ex,events,logs,fn⟩
    intro τ i rootNe resultNe
    rw [source_locals_get_set_other changed.1 result i _ resultNe,locals]
    exact source_locals_get_set_other y.1 dst i _ rootNe

/-- info: 'Solidity.Backend.MemoryOps.source_items_triple_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_items_triple_error
/-- info: 'Solidity.Backend.MemoryOps.source_uint_slice_bind_add_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_slice_bind_add_read
end Solidity.Backend.MemoryOps
