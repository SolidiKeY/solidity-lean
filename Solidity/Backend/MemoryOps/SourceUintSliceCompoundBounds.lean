import Solidity.Backend.MemoryOps.SourceUintSliceCompound

/-! Dynamic Source compound bounds rejection, composed with actual slice
binding. Lvalue bounds precede old-cell arithmetic after the pure-local RHS;
no successful suffix, transaction rollback or word panic payload is assumed. -/
namespace Solidity.Backend.MemoryOps

/-- Initial typed alignment derives the actual index panic before old-cell
reading/arithmetic/write. This keeps genuine dynamic Source array type none;
the intrinsic ArrTy may be any existing primitive array representation. -/
theorem SourceUintMemoryAt.compound_add_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ SourceUintArrayTy) (index rhs : Source.Idx Γ (.int .u256))
    (k value : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hi : y.1.get index=sourceUint k) (hv : y.1.get rhs=sourceUint value)
    (outside : hp.len r a≤k.1.toNat) :
    (Source.evalE G F (fuel+3) (sourceUintIndexedAdd root index rhs)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  first
  | solve | simp only [] | omega
  | rw [sourceUintIndexedAdd,Source.evalE,Source.Hoare.run_bind,
      source_local_value_run G F (fuel+1) y rhs _ hv]
    simp only [Source.Hoare.run_bind]
    rw [hr.eval_index_bounds G F fuel root index k hroot hi outside]

/-- Only a low-horizon timeout is claimed, not minimal successful fuel. -/
theorem source_uint_add_low {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ SourceUintArrayTy) (index rhs : Source.Idx Γ (.int .u256)) :
    ∀ fuel,fuel≤2 → (Source.evalE G F fuel (sourceUintIndexedAdd root index rhs)).run y=(.error .timeout,y) := by
  intro fuel low
  match fuel with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | fuel+3 => omega

/-- The successful binding really allocates the computed window. Its reached
length and unchanged scalar locals derive the suffix rejection, without any
arithmetic guard or assumed failure run. Items retains reached globals while
erasing returned locals on error. Native bounds reject every attempted value. -/
theorem source_uint_slice_bind_add_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
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
      (Source.evalE G F (fuel+3) (sourceUintIndexedAdd dst index rhs)).run mid=
        (.error (.revert (Source.panicData .index)),mid) ∧
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintSliceBind dst root start finish toEnd))
          (.stmt (.expr (sourceUintIndexedAdd dst index rhs)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
      pair.1.readAddr (.index pair.2 .dyn k)=none ∧
      (∀ v : PrimTy.uint.Denote,pair.1.writeAddr (.index pair.2 .dyn k) v=none) ∧
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
    have rhsNe : dst.toNat≠rhs.toNat := by
      intro same
      cases source_idx_type_of_position dst rhs same
    have rhsValue := (other (.int .u256) rhs rhsNe).trans hv
    have second := fresh.compound_add_bounds G F fuel dst index rhs k value selected indexValue rhsValue outside
    have nativeRead : pair.1.readAddr (.index pair.2 .dyn k)=none := List.getElem?_eq_none outside
    have nativeWrite : ∀ v : PrimTy.uint.Denote,pair.1.writeAddr (.index pair.2 .dyn k) v=none := by
      intro v
      simp only [Heap.writeAddr,Heap.setIndex,show ¬k.1.toNat<(MObj.elems .dyn (pair.1.get pair.2)).length from Nat.not_lt.mpr outside,↓reduceIte]
    have secondStatement := source_expr_statement_error G F (fuel+3) nps _ _ _ _ second
    refine ⟨first,second,source_items_pair_error G F fuel nps _ _ _ _ _ _ firstStatement secondStatement,
      nativeRead,nativeWrite,fresh,mok,keep,?_⟩
    intro b obj hb
    exact (preserved b obj hb).1

/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.compound_add_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.compound_add_bounds
/-- info: 'Solidity.Backend.MemoryOps.source_uint_add_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_add_low
/-- info: 'Solidity.Backend.MemoryOps.source_uint_slice_bind_add_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_slice_bind_add_bounds
end Solidity.Backend.MemoryOps
