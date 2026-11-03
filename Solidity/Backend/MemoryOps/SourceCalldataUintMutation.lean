import Solidity.Backend.MemoryOps.SourceCalldataUintBinding
import Solidity.Backend.MemoryOps.SourceUintAssignment

/-! Actual reached uint mutation after raw-input copy/local binding. Existing
Source/intrinsic operations and frames are composed, not reimplemented.
No intrinsic-local or emitted fresh-copy program is asserted. -/
namespace Solidity.Backend.MemoryOps

theorem SourceUintMemoryAt.write_observed {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (F : Source.Fr) (fuel : Nat) (i value : PrimTy.uint.Denote)
    (bound : i.1.toNat<hp.len r a) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r a i) value=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.1.toNat) (sourceUint value)).run y=(.ok (),z) ∧
      SourceUintMemoryAt z address out r a ∧ Source.MemOK E SH z ∧
      MObj.elems a (out.get r)=(MObj.elems a (hp.get r)).set i.1.toNat value ∧
      (∀ Q (q : HRef H Q),r.id≠q.id → out.get q=hp.get q) ∧
      (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
      z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  obtain ⟨out,z,hw,hs,new⟩ := hr.write_addr F fuel i value bound
  obtain ⟨locals,frames,sourceFrames,aliases,ex,events,logs,fn⟩ := hr.write_frames F fuel i value bound hw hs
  have mok := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F fuel
    (.mem (τ := .int .u256) address i.1.toNat) (sourceUint value) y ⟨hm,trivial⟩
  rw [hs] at mok
  refine ⟨out,z,hw,hs,new,mok,indexedWrite_elems hp out r a i value hw,?_,sourceFrames,locals,ex,events,logs,fn⟩
  intro Q q ne
  exact frames q ne

/-- Initial scalar alignment and the ACTUAL computed copy length suffice for
ONE Source program to copy/bind then mutate the selected fresh uint array. -/
theorem source_cd_uint_bind_assign {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none))
    (index rhs : Source.Idx Γ (.int .u256)) (off len : Nat) (k value : PrimTy.uint.Denote)
    (hsrc : y.1.get src=.cdRef rfl off len) (hi : y.1.get index=sourceUint k)
    (hv : y.1.get rhs=sourceUint value) (bound : k.1.toNat<len) (cap : len<2^256)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    match sourceCalldataUintValues E F off len with
    | .error error =>
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedAssign dst index rhs)) .nil) :
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
        (Source.evalE G F (fuel+3) (sourceUintIndexedAssign dst index rhs)).run mid=(.ok (.val (sourceUint value)),z) ∧
        (Source.execItems G F (fuel+6) nps none
          (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintIndexedAssign dst index rhs)) .nil) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
        checkedSourceFreshUints (E := E) F off len hp cap=.ok (some pair.1) ∧
        pair.1.writeAddr (.index pair.2 .dyn k) value=some out ∧
        SourceUintMemoryAt z y.2.heap.next out pair.2 .dyn ∧ Source.MemOK E SH z ∧
        Heap.Keeps ext hp out ∧ MObj.elems .dyn (out.get pair.2)=(sourceUintValuePayload vs).set k.1.toNat value ∧
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
    have rhsNe : dst.toNat≠rhs.toNat := by
      intro same
      cases source_idx_type_of_position dst rhs same
    have indexValue := (other (.int .u256) index indexNe).trans hi
    have rhsValue := (other (.int .u256) rhs rhsNe).trans hv
    obtain ⟨out,z,hw,hs,new,hmz,values,frames,sourceFrames,locals,exz,eventsz,logsz,fnz⟩ :=
      fresh.write_observed F (fuel+2) k value inBounds SH mok
    have second := fresh.eval_assign_of_run G F fuel dst index rhs k value selected indexValue rhsValue inBounds hs
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
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.write_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SourceUintMemoryAt.write_observed
/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_bind_assign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cd_uint_bind_assign
end Solidity.Backend.MemoryOps
