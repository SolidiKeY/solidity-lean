import Solidity.Backend.MemoryOps.SourceCalldataUintBinding

/-! Actual uint copy/binding followed by Boolean copy at its reached heap.
Existing operations, observers and allocators are composed, not replaced. -/
namespace Solidity.Backend.MemoryOps

/-- The two real Source operations preserve their order, separate typed fresh
identities, computed payloads, original occupied objects and failure boundary. -/
theorem source_cd_uint_bind_bool_copy {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (usrc : Source.Idx Γ (.array .calldata (.int .u256) none))
    (bsrc : Source.Idx Γ (.array .calldata .bool none)) (uo ul bo bl : Nat)
    (hu : y.1.get usrc=.cdRef rfl uo ul) (hb : y.1.get bsrc=.cdRef rfl bo bl)
    (ucap : ul<2^256) (bcap : bl<2^256) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    match sourceCalldataUintValues E F uo ul with
    | .error error =>
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintCalldataBind dst usrc)) (.stmt (.expr (sourceBoolCalldataCopy bsrc)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.error error,(.nil,y.2))
    | .ok us => ∃ uv : (sourceUintValuePayload us).length<2^256,
      let up := hp.alloc (R := .array (.prim .uint))
        (⟨sourceUintValuePayload us,uv⟩ : MObj H (.array (.prim .uint)))
      let ue := List.prefix_append H [RefTy.array (.prim .uint)]
      let mid : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (sourceUintValuePayload us)⟩).1})
      (Source.evalE G F (fuel+4) (sourceUintCalldataBind dst usrc)).run y=
        (.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
      checkedSourceFreshUints (E := E) F uo ul hp ucap=.ok (some up.1) ∧
      Heap.Keeps ue hp up.1 ∧ SourceUintMemoryAt mid y.2.heap.next up.1 up.2 .dyn ∧ Source.MemOK E SH mid ∧
      match sourceCalldataBoolValues E F bo bl with
      | .error error =>
        (Source.evalE G F (fuel+3) (sourceBoolCalldataCopy bsrc)).run mid=(.error error,mid) ∧
        (Source.execItems G F (fuel+6) nps none
          (.stmt (.expr (sourceUintCalldataBind dst usrc)) (.stmt (.expr (sourceBoolCalldataCopy bsrc)) .nil) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.error error,(.nil,mid.2)) ∧
        checkedSourceFreshBools (E := E) F bo bl up.1 bcap=.error error
      | .ok bs => ∃ bv : (sourceBoolValuePayload bs).length<2^256,
        let bp := up.1.alloc (R := .array (.prim .bool))
          (⟨sourceBoolValuePayload bs,bv⟩ : MObj (H++[RefTy.array (.prim .uint)]) (.array (.prim .bool)))
        let be := List.prefix_append (H++[RefTy.array (.prim .uint)]) [RefTy.array (.prim .bool)]
        let z : Source.EMState E Γ :=
          (mid.1,{mid.2 with heap := (mid.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (sourceBoolValuePayload bs)⟩).1})
        (Source.evalE G F (fuel+3) (sourceBoolCalldataCopy bsrc)).run mid=
          (.ok (.val (.memRef rfl mid.2.heap.next)),z) ∧
        (Source.execItems G F (fuel+6) nps none
          (.stmt (.expr (sourceUintCalldataBind dst usrc)) (.stmt (.expr (sourceBoolCalldataCopy bsrc)) .nil) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
        checkedSourceFreshBools (E := E) F bo bl up.1 bcap=.ok (some bp.1) ∧
        Heap.Keeps be up.1 bp.1 ∧
        SourceUintMemoryAt z y.2.heap.next bp.1 (up.2.wk be) .dyn ∧
        SourceBoolMemoryAt z mid.2.heap.next bp.1 bp.2 .dyn ∧ Source.MemOK E SH z ∧
        (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj) ∧
        up.2.id=H.length ∧ bp.2.id=H.length+1 ∧ up.2.id≠bp.2.id ∧
        y.2.heap.next≠mid.2.heap.next ∧ z.1=mid.1 ∧
        z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  have firstResult := source_cd_uint_bind_copy y hp G F (fuel+1) nps dst usrc uo ul hu ucap SH hm
  cases ud : sourceCalldataUintValues E F uo ul with
  | error error =>
    rw [ud] at firstResult
    rw [Source.execItems,Source.Hoare.run_bind,firstResult.2]
  | ok us =>
    rw [ud] at firstResult
    obtain ⟨uv,first,firstStmt,uadapter,ukeep,urepr,umok,selected,other,uid,oldSource,ex,events,logs,fn⟩ := firstResult
    refine ⟨uv,?_⟩
    dsimp only
    let up := hp.alloc (R := .array (.prim .uint))
      (⟨sourceUintValuePayload us,uv⟩ : MObj H (.array (.prim .uint)))
    let mid : Source.EMState E Γ :=
      (y.1.set dst (.memRef rfl y.2.heap.next),
        {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (sourceUintValuePayload us)⟩).1})
    refine ⟨first,uadapter,ukeep,urepr,umok,?_⟩
    have indexNe : dst.toNat≠bsrc.toNat := by
      intro same
      cases source_idx_type_of_position dst bsrc same
    have aligned := (other (.array .calldata .bool none) bsrc indexNe).trans hb
    have second := source_cd_bool_eval G F (fuel+1) mid bsrc bo bl aligned
    rw [source_cd_bool_run] at second
    cases bd : sourceCalldataBoolValues E F bo bl with
    | error error =>
      rw [bd] at second
      have secondStmt := source_expr_statement_error G F (fuel+3) nps _ mid mid error second
      exact ⟨second,source_items_pair_error G F fuel nps _ _ y mid mid error firstStmt secondStmt,
        checkedSourceFreshBools_error F bo bl up.1 bcap error bd⟩
    | ok bs =>
      rw [bd] at second
      obtain ⟨bv,direct,badapter⟩ := checkedSourceFreshBools_some F bo bl up.1 bcap bs bd
      refine ⟨bv,?_⟩
      dsimp only
      let o : MObj (H++[RefTy.array (.prim .uint)]) (.array (.prim .bool)) :=
        ⟨sourceBoolValuePayload bs,bv⟩
      let bp := up.1.alloc o
      let be := List.prefix_append (H++[RefTy.array (.prim .uint)]) [RefTy.array (.prim .bool)]
      let z : Source.EMState E Γ :=
        (mid.1,{mid.2 with heap := (mid.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (sourceBoolValuePayload bs)⟩).1})
      have keep : Heap.Keeps be up.1 bp.1 := up.1.keeps_alloc o
      have occupied : ∀ b obj,mid.2.heap.get b=some obj → z.2.heap.get b=some obj := by
        intro b obj hit
        have different : b≠mid.2.heap.next := by
          intro same
          have free : mid.2.heap.get mid.2.heap.next=none := mid.2.heap.bounded _ (Nat.le_refl _)
          rw [same,free] at hit
          cases hit
        exact (Source.Heap.alloc_other mid.2.heap _ different).trans hit
      have finalU : SourceUintMemoryAt z y.2.heap.next bp.1 (up.2.wk be) .dyn := urepr.transport keep occupied
      have finalB : SourceBoolMemoryAt z mid.2.heap.next bp.1 bp.2 .dyn := by
        unfold SourceBoolMemoryAt
        rw [up.1.get_alloc o,MObj.elems_wk,List.map_id'' (f := MVal.wk be (.prim .bool)) (fun _ => rfl)]
        rw [MObj.elems_dyn]
        exact Source.Heap.alloc_get mid.2.heap _
      have mok := source_bool_alloc_memOK (E := E) (Γ := Γ) SH (sourceBoolValuePayload bs) mid umok
      rw [source_bool_alloc mid (sourceBoolValuePayload bs)] at mok
      have secondStmt := source_expr_statement_run G F (fuel+3) nps _ mid z _ second
      refine ⟨second,source_items_pair_run G F fuel nps _ _ y mid z firstStmt secondStmt,
        badapter,keep,finalU,finalB,mok.1,?_,rfl,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
      · intro b obj hit
        exact occupied b obj (oldSource b obj hit).1
      · change (H++[RefTy.array (.prim .uint)]).length=H.length+1
        simp only [List.length_append,List.length_singleton]
      · change H.length≠(H++[RefTy.array (.prim .uint)]).length
        simp only [List.length_append,List.length_singleton]
        omega
      · change y.2.heap.next≠y.2.heap.next+1
        omega

/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_bind_bool_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_cd_uint_bind_bool_copy
end Solidity.Backend.MemoryOps
