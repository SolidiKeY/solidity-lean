import Solidity.Backend.MemoryOps.SourceCalldataUintMutation
import Solidity.Backend.MemoryOps.SourceUintDelete

/-! Actual deletion after raw-input copy and binding. Source default/unit and
checked native writes are separate linked operations; no emitted copy claim. -/
namespace Solidity.Backend.MemoryOps

/-- Actual copied payload and initial index alignment derive deletion at the
reached fresh object; all old objects and occupied Source cells are framed. -/
theorem source_cd_uint_bind_delete {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none))
    (index : Source.Idx Γ (.int .u256)) (off len : Nat) (k : PrimTy.uint.Denote)
    (hsrc : y.1.get src=.cdRef rfl off len) (hi : y.1.get index=sourceUint k)
    (bound : k.1.toNat<len) (cap : len<2^256)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    match sourceCalldataUintValues E F off len with
    | .error error =>
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.error error,(.nil,y.2))
    | .ok vs => ∃ valid : (sourceUintValuePayload vs).length<2^256,
      let pair := hp.alloc (R := .array (.prim .uint))
        (⟨sourceUintValuePayload vs,valid⟩ : MObj H (.array (.prim .uint)))
      let ext := List.prefix_append H [RefTy.array (.prim .uint)]
      let mid : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (sourceUintValuePayload vs)⟩).1})
      ∃ (out : Heap (H++[RefTy.array (.prim .uint)])) (z : Source.EMState E Γ),
        (Source.evalE G F (fuel+4) (sourceUintCalldataBind dst src)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
        (Source.evalE G F (fuel+3) (sourceUintIndexedDelete dst index)).run mid=(.ok Source.RVal.unit,z) ∧
        (Source.execItems G F (fuel+6) nps none
          (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
        checkedSourceFreshUints (E := E) F off len hp cap=.ok (some pair.1) ∧
        pair.1.writeAddr (.index pair.2 .dyn k) (PrimTy.dflt .uint)=some out ∧
        SourceUintMemoryAt z y.2.heap.next out pair.2 .dyn ∧ Source.MemOK E SH z ∧
        Heap.Keeps ext hp out ∧ MObj.elems .dyn (out.get pair.2)=(sourceUintValuePayload vs).set k.1.toNat (PrimTy.dflt .uint) ∧
        (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj) ∧
        z.1=mid.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  have binding := source_cd_uint_bind_copy y hp G F (fuel+1) nps dst src off len hsrc cap SH hm
  cases decoded : sourceCalldataUintValues E F off len with
  | error error =>
    rw [decoded] at binding
    rw [Source.execItems,Source.Hoare.run_bind,binding.2]
  | ok vs =>
    rw [decoded] at binding
    obtain ⟨valid,first,firstStatement,adapter,keep,fresh,mok,selected,other,identity,preserved,ex,events,logs,fn⟩ := binding
    refine ⟨valid,?_⟩
    dsimp only
    let pair := hp.alloc (R := .array (.prim .uint))
      (⟨sourceUintValuePayload vs,valid⟩ : MObj H (.array (.prim .uint)))
    let ext := List.prefix_append H [RefTy.array (.prim .uint)]
    have elements : MObj.elems .dyn (pair.1.get pair.2)=sourceUintValuePayload vs := by
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
      exact List.map_id'' (fun _ => rfl) _
    have size : pair.1.len pair.2 .dyn=len := by
      unfold Heap.len
      rw [elements,sourceCalldataUintValues_length decoded]
    have inBounds : k.1.toNat<pair.1.len pair.2 .dyn := by rw [size];exact bound
    have indexNe : dst.toNat≠index.toNat := by
      intro same
      cases source_idx_type_of_position dst index same
    have indexValue := (other (.int .u256) index indexNe).trans hi
    obtain ⟨out,z,hw,hs,new,hmz,values,frames,sourceFrames,locals,exz,eventsz,logsz,fnz⟩ :=
      fresh.write_observed F (fuel+2) k (PrimTy.dflt .uint) inBounds SH mok
    have second := fresh.eval_delete_of_run G F fuel dst index k selected indexValue inBounds hs
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
      adapter,hw,new,hmz,keeps,?_,occupied,locals,exz.trans ex,eventsz.trans events,logsz.trans logs,fnz.trans fn⟩
    rw [elements] at values
    exact values

/-- A successful allocation/binding prefix is retained when the actual fresh
length rejects the delete index. No suffix heap or local environment is invented. -/
theorem source_cd_uint_bind_delete_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none))
    (index : Source.Idx Γ (.int .u256)) (off len : Nat) (k : PrimTy.uint.Denote)
    (hsrc : y.1.get src=.cdRef rfl off len) (hi : y.1.get index=sourceUint k)
    (bound : len≤k.1.toNat) (cap : len<2^256)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    match sourceCalldataUintValues E F off len with
    | .error error =>
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.error error,(.nil,y.2))
    | .ok vs => ∃ valid : (sourceUintValuePayload vs).length<2^256,
      let pair := hp.alloc (R := .array (.prim .uint))
        (⟨sourceUintValuePayload vs,valid⟩ : MObj H (.array (.prim .uint)))
      let mid : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (sourceUintValuePayload vs)⟩).1})
      (Source.evalE G F (fuel+4) (sourceUintCalldataBind dst src)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
      (Source.evalE G F (fuel+3) (sourceUintIndexedDelete dst index)).run mid=
        (.error (.revert (Source.panicData .index)),mid) ∧
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedDelete dst index)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
      checkedSourceFreshUints (E := E) F off len hp cap=.ok (some pair.1) ∧
      pair.1.writeAddr (.index pair.2 .dyn k) (PrimTy.dflt .uint)=none ∧
      SourceUintMemoryAt mid y.2.heap.next pair.1 pair.2 .dyn ∧ Source.MemOK E SH mid ∧
      Heap.Keeps (List.prefix_append H [RefTy.array (.prim .uint)]) hp pair.1 ∧
      (∀ b obj,y.2.heap.get b=some obj → mid.2.heap.get b=some obj) := by
  have binding := source_cd_uint_bind_copy y hp G F (fuel+1) nps dst src off len hsrc cap SH hm
  cases decoded : sourceCalldataUintValues E F off len with
  | error error =>
    rw [decoded] at binding
    rw [Source.execItems,Source.Hoare.run_bind,binding.2]
  | ok vs =>
    rw [decoded] at binding
    obtain ⟨valid,first,firstStatement,adapter,keep,fresh,mok,selected,other,identity,preserved,ex,events,logs,fn⟩ := binding
    refine ⟨valid,?_⟩
    dsimp only
    let pair := hp.alloc (R := .array (.prim .uint))
      (⟨sourceUintValuePayload vs,valid⟩ : MObj H (.array (.prim .uint)))
    have elements : MObj.elems .dyn (pair.1.get pair.2)=sourceUintValuePayload vs := by
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
      exact List.map_id'' (fun _ => rfl) _
    have size : pair.1.len pair.2 .dyn=len := by
      unfold Heap.len
      rw [elements,sourceCalldataUintValues_length decoded]
    have outside : pair.1.len pair.2 .dyn≤k.1.toNat := by rw [size];exact bound
    have indexNe : dst.toNat≠index.toNat := by
      intro same
      cases source_idx_type_of_position dst index same
    have indexValue := (other (.int .u256) index indexNe).trans hi
    let mid : Source.EMState E Γ :=
      (y.1.set dst (.memRef rfl y.2.heap.next),
        {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (sourceUintValuePayload vs)⟩).1})
    have second : (Source.evalE G F (fuel+3) (sourceUintIndexedDelete dst index)).run mid=
        (.error (.revert (Source.panicData .index)),mid) := by
      rw [sourceUintIndexedDelete,Source.evalE,Source.Hoare.run_bind,
        fresh.eval_index_bounds G F fuel dst index k selected indexValue outside]
    have secondStatement := source_expr_statement_error G F (fuel+3) nps _ _ _ _ second
    refine ⟨first,second,source_items_pair_error G F fuel nps _ _ _ _ _ _ firstStatement secondStatement,
      adapter,(fresh.delete_bounds F fuel k outside).2,fresh,mok,keep,?_⟩
    intro b obj hb
    exact (preserved b obj hb).1

/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_bind_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_cd_uint_bind_delete
/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_bind_delete_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_cd_uint_bind_delete_bounds
end Solidity.Backend.MemoryOps
