import Solidity.Backend.MemoryOps.SourceCalldataBinding
import Solidity.Backend.MemoryOps.SourceAssignment

/-! Reached Source mutation after actual raw-input copy/local binding. Existing
Source/intrinsic operations and frame laws are composed, not reimplemented.
No intrinsic-local or emitted fresh-copy program is asserted here. -/
namespace Solidity.Backend.MemoryOps

/-- Equal typed local positions have equal types, with no address premise. -/
theorem source_idx_type_of_position : {Γ : Source.RCtx} → {τ υ : Source.STy} →
    (i : Source.Idx Γ τ) → (j : Source.Idx Γ υ) → i.toNat=j.toNat → τ=υ
  | _,_,_,.here,.here,_ => rfl
  | _,_,_,.here,.there j,same => by simp only [Source.Idx.toNat] at same;omega
  | _,_,_,.there i,.here,same => by simp only [Source.Idx.toNat] at same;omega
  | _,_,_,.there i,.there j,same => source_idx_type_of_position i j (Nat.add_right_cancel same)

/-- Existing write_addr supplies the actual runs. Existing indexed-write laws
and Source heap laws expose complete local, object, address and world frames. -/
theorem SourceBoolMemoryAt.write_observed {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (value : Bool)
    (bound : i.1.toNat<hp.len r a) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r a i) value=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.1.toNat) (.bool value)).run y=(.ok (),z) ∧
      SourceBoolMemoryAt z address out r a ∧ Source.MemOK E SH z ∧
      MObj.elems a (out.get r)=(MObj.elems a (hp.get r)).set i.1.toNat value ∧
      (∀ Q (q : HRef H Q),r.id≠q.id → out.get q=hp.get q) ∧
      (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
      z.1=y.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  obtain ⟨out,z,hw,hs,new⟩ := hr.write_addr F fuel i value bound
  obtain ⟨ht,actual⟩ := source_bool_write y address _ hr i.1.toNat bound value
  have state : z=(y.1,{y.2 with heap := y.2.heap.write address (sourceBoolMemory ((MObj.elems a (hp.get r)).set i.1.toNat value)) ht}) :=
    congrArg Prod.snd (hs.symm.trans actual)
  have mok := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F fuel
    (.mem (τ := .bool) address i.1.toNat) (.bool value) y ⟨hm,trivial⟩
  rw [hs] at mok
  refine ⟨out,z,hw,hs,new,mok,indexedWrite_elems hp out r a i value hw,?_,?_,?_,?_,?_,?_,?_⟩
  · intro Q q ne;exact indexedWrite_frame hp out r a i value hw q ne
  · intro b ne;rw [state];exact Source.Heap.write_other y.2.heap ne _ ht
  all_goals rw [state]

/-- The second statement consumes the ACTUAL freshly bound object. Initial
scalar alignment and the computed copy length suffice; every old occupied
Source object and old intrinsic object is derived to survive the mutation. -/
theorem SourceBoolStructAt.bind_cd_bool_assign {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y addr hp r address layout)
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat)
    (dst : Source.Idx Γ SourceBoolArrayTy) (src : Source.Idx Γ (.array .calldata .bool none))
    (index : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ .bool)
    (off len : Nat) (k : PrimTy.uint.Denote) (value : Bool)
    (hsrc : y.1.get src=.cdRef rfl off len) (hi : y.1.get index=sourceUint k) (hv : y.1.get rhs=.bool value)
    (bound : k.1.toNat<len) (cap : len<2^256) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    match sourceCalldataBoolValues E F off len with
    | .error e =>
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceBoolCalldataBind dst src)) (.stmt (.expr (sourceIndexedAssign dst index rhs)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.error e,(.nil,y.2))
    | .ok vs => ∃ valid : (sourceBoolValuePayload vs).length<2^256,
      let o : MObj H (.array (.prim .bool)) := ⟨sourceBoolValuePayload vs,valid⟩
      let pair := hp.alloc o
      let ext := List.prefix_append H [RefTy.array (.prim .bool)]
      let address' := allocatedSourceAddress address H.length y.2.heap.next
      let mid : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (sourceBoolValuePayload vs)⟩).1})
      ∃ (out : Heap (H++[RefTy.array (.prim .bool)])) (z : Source.EMState E Γ),
        (Source.evalE G F (fuel+4) (sourceBoolCalldataBind dst src)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
        (Source.evalE G F (fuel+3) (sourceIndexedAssign dst index rhs)).run mid=(.ok (.val (.bool value)),z) ∧
        (Source.execItems G F (fuel+6) nps none
          (.stmt (.expr (sourceBoolCalldataBind dst src)) (.stmt (.expr (sourceIndexedAssign dst index rhs)) .nil) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
        checkedSourceFreshBools (E := E) F off len hp cap=.ok (some pair.1) ∧
        pair.1.writeAddr (.index pair.2 .dyn k) value=some out ∧
        SourceBoolMemoryAt z y.2.heap.next out pair.2 .dyn ∧ Source.MemOK E SH z ∧
        Heap.Keeps ext hp out ∧ SourceBoolStructAt z addr out (r.wk ext) address' layout ∧
        MObj.elems .dyn (out.get pair.2)=(sourceBoolValuePayload vs).set k.1.toNat value ∧
        (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj) ∧
        z.1=mid.1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  have copied := hr.bind_cd_bool_copy G F (fuel+1) nps dst src off len hsrc cap SH hm
  cases decoded : sourceCalldataBoolValues E F off len with
  | error err =>
    rw [decoded] at copied
    rw [Source.execItems,Source.Hoare.run_bind,copied.2]
  | ok vs =>
    rw [decoded] at copied
    obtain ⟨valid,first,firstStatement,adapter,keep,_,fresh,mok,selected,other,_,_,_⟩ := copied
    let o : MObj H (.array (.prim .bool)) := ⟨sourceBoolValuePayload vs,valid⟩
    let pair := hp.alloc o
    let ext := List.prefix_append H [RefTy.array (.prim .bool)]
    have elements : MObj.elems .dyn (pair.1.get pair.2)=sourceBoolValuePayload vs := by
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
      exact List.map_id'' (fun _ => rfl) _
    have size : pair.1.len pair.2 .dyn=len := by
      unfold Heap.len
      rw [elements,sourceCalldataBoolValues_length decoded]
    have inBounds : k.1.toNat<pair.1.len pair.2 .dyn := by rw [size];exact bound
    have differentIndex : dst.toNat≠index.toNat := by
      intro same;cases source_idx_type_of_position dst index same
    have differentValue : dst.toNat≠rhs.toNat := by
      intro same;cases source_idx_type_of_position dst rhs same
    have indexValue := (other (.int .u256) index differentIndex).trans hi
    have rhsValue := (other .bool rhs differentValue).trans hv
    obtain ⟨out,z,hw,hs,new,hmz,values,frames,sourceFrames,locals,ex,events,logs,fn⟩ :=
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
      have different : b≠y.2.heap.next := by
        intro same
        subst b
        have vacant := Source.Heap.alloc_fresh y.2.heap ⟨SourceBoolArrayTy,sourceBoolMemory (sourceBoolValuePayload vs)⟩
        change y.2.heap.get y.2.heap.next=none at vacant
        rw [vacant] at hb
        cases hb
      rw [sourceFrames b different]
      exact (Source.Heap.alloc_other y.2.heap _ different).trans hb
    refine ⟨valid,out,z,first,second,source_items_pair_run G F fuel nps _ _ _ _ _ firstStatement secondStatement,
      adapter,hw,new,hmz,keeps,hr.transport keeps occupied (allocatedSourceAddress_old address y.2.heap.next),?_,
      occupied,locals,ex,events,logs,fn⟩
    rw [elements] at values
    exact values

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.bind_cd_bool_assign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.bind_cd_bool_assign
/-- info: 'Solidity.Backend.MemoryOps.source_idx_type_of_position' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_idx_type_of_position
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.write_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolMemoryAt.write_observed
end Solidity.Backend.MemoryOps
