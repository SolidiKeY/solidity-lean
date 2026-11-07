import Solidity.Backend.MemoryOps.SourceCalldataUintTransfer
import Solidity.Backend.MemoryOps.SourceCalldataMutation

/-! Actual Source numeric copy/local binding and reached read composition.
Existing assignment, copy and sequence semantics are consumed. No intrinsic
local context, emitted fresh allocator or target representation is assumed. -/
namespace Solidity.Backend.MemoryOps

abbrev SourceUintArrayTy : Source.STy := .array .memory (.int .u256) none

def sourceUintCalldataBind {E : Source.Env} {Γ : Source.RCtx}
    (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none)) : Source.RExpr E Γ SourceUintArrayTy :=
  .assign (.local dst) (sourceUintCalldataCopy src)

theorem source_cd_uint_bind_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none))
    (off len : Nat) (hs : y.1.get src=.cdRef rfl off len) :
    (Source.evalE G F (fuel+3) (sourceUintCalldataBind dst src)).run y=
      match sourceCalldataUintValues E F off len with
      | .error error => (.error error,y)
      | .ok vs =>
        let z : Source.EMState E Γ :=
          (y.1.set dst (.memRef rfl y.2.heap.next),
            {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (sourceUintValuePayload vs)⟩).1})
        (.ok (.val (.memRef rfl y.2.heap.next)),z) := by
  unfold sourceUintCalldataBind
  rw [Source.evalE,Source.Hoare.run_bind,source_cd_uint_eval G F fuel y src off len hs,source_cd_uint_run]
  cases decoded : sourceCalldataUintValues E F off len with
  | error error => rfl
  | ok vs =>
    dsimp only
    rw [Source.Hoare.run_bind]
    rfl

theorem SourceUintMemoryAt.bind_memOK {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (dst : Source.Idx Γ SourceUintArrayTy) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    Source.MemOK E SH (y.1.set dst (.memRef rfl address),y.2) := by
  have hv : Source.Val.RefOK E y.2.heap.ty
      (.memRef rfl address : Source.Val E.layout SourceUintArrayTy) := by
    refine ⟨SourceUintArrayTy,?_,rfl⟩
    change (y.2.heap.get address).map Sigma.fst=some SourceUintArrayTy
    rw [hr]
    rfl
  exact ⟨⟨hm.1.1,Source.LocalsOK.set y.1 dst hm.1.2 hv⟩,hm.2⟩

/-- The local now names the computed fresh object; all other locals, old heap
objects, occupied Source cells and world fields follow the actual executions. -/
theorem source_cd_uint_bind_copy {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H)
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat)
    (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none))
    (off len : Nat) (hsrc : y.1.get src=.cdRef rfl off len) (cap : len<2^256)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    match sourceCalldataUintValues E F off len with
    | .error error =>
      (Source.evalE G F (fuel+3) (sourceUintCalldataBind dst src)).run y=(.error error,y) ∧
      (Source.execS G F (fuel+4) nps none
        (.expr (sourceUintCalldataBind dst src) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error error,(.nil,y.2))
    | .ok vs => ∃ valid : (sourceUintValuePayload vs).length<2^256,
      let pair := hp.alloc (R := .array (.prim .uint)) (⟨sourceUintValuePayload vs,valid⟩ : MObj H (.array (.prim .uint)))
      let ext := List.prefix_append H [RefTy.array (.prim .uint)]
      let z : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (sourceUintValuePayload vs)⟩).1})
      (Source.evalE G F (fuel+3) (sourceUintCalldataBind dst src)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),z) ∧
      (Source.execS G F (fuel+4) nps none
        (.expr (sourceUintCalldataBind dst src) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      checkedSourceFreshUints (E := E) F off len hp cap=.ok (some pair.1) ∧
      Heap.Keeps ext hp pair.1 ∧ SourceUintMemoryAt z y.2.heap.next pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
      z.1.get dst=.memRef rfl y.2.heap.next ∧
      (∀ τ (i : Source.Idx Γ τ),dst.toNat≠i.toNat → z.1.get i=y.1.get i) ∧
      pair.2.id=H.length ∧
      (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj ∧ b≠y.2.heap.next) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  have run := source_cd_uint_bind_run G F fuel y dst src off len hsrc
  have paired := source_cd_uint_checked_copy y hp id F off len cap SH hm
  cases decoded : sourceCalldataUintValues E F off len with
  | error error =>
    rw [decoded] at run
    exact ⟨run,source_expr_statement_error G F (fuel+3) nps _ y y error run⟩
  | ok vs =>
    rw [decoded] at run paired
    obtain ⟨valid,direct,adapter,sourceRun,keep,new,mok,preserved,loc,ex,events,logs,fn⟩ := paired
    have freshAddress : allocatedSourceAddress id H.length y.2.heap.next
        (hp.alloc (R := .array (.prim .uint)) (⟨sourceUintValuePayload vs,valid⟩ : MObj H (.array (.prim .uint)))).2.id=
        y.2.heap.next := if_pos rfl
    rw [freshAddress] at new
    have boundOK := new.bind_memOK dst SH mok
    refine ⟨valid,run,source_expr_statement_run G F (fuel+3) nps _ y _ _ run,
      adapter,keep,new,boundOK,source_locals_get_set _ _ _,?_,rfl,preserved,rfl,rfl,rfl,rfl⟩
    intro τ i ne
    exact source_locals_get_set_other y.1 dst i _ ne

/-- Exact Source read-expression bounds at a represented numeric object. -/
theorem SourceUintMemoryAt.eval_read_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ SourceUintArrayTy) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (bound : hp.len r a≤k.1.toNat) :
    (Source.evalE G F (fuel+2) (.indexArray (.local root) (.local index) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F fuel y root _ hroot]
  change ((Source.evalE G F (fuel+1) (.local index)) >>= fun v => Source.indexNat v >>= fun n =>
    Source.indexLoc F (.memRef rfl address : Source.Val E.layout SourceUintArrayTy) n >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y index _ hindex]
  change (Source.indexLoc F (.memRef rfl address : Source.Val E.layout SourceUintArrayTy) k.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.indexLoc_bounds F _ bound]

theorem source_cd_uint_bind_low {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none)) :
    ∀ fuel,fuel≤2 → (Source.evalE G F fuel (sourceUintCalldataBind dst src)).run y=(.error .timeout,y) := by
  intro fuel low
  match fuel with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | fuel+3 => omega
/-- Existing Source assignment stores the actual reached indexed read. The
result slot may equal the index slot: the RHS reads its prior value first. -/
def sourceUintReadInto {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ SourceUintArrayTy) (index result : Source.Idx Γ (.int .u256)) :
    Source.RExpr E Γ (.int .u256) :=
  .assign (.local result) (.indexArray (.local root) (.local index) rfl)

theorem source_uint_read_into_of_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ SourceUintArrayTy) (index result : Source.Idx Γ (.int .u256))
    (value : PrimTy.uint.Denote)
    (read : (Source.evalE G F (fuel+2) (.indexArray (.local root) (.local index) rfl)).run y=
      (.ok (.val (sourceUint value)),y)) :
    (Source.evalE G F (fuel+3) (sourceUintReadInto root index result)).run y=
      (.ok (.val (sourceUint value)),(y.1.set result (sourceUint value),y.2)) := by
  unfold sourceUintReadInto
  rw [Source.evalE,Source.Hoare.run_bind,read]
  dsimp only
  rw [Source.Hoare.run_bind]
  rfl

/-- ONE Source RItems program: actual copy and pointer binding, followed by a
read of that reached fresh object stored in a scalar. Initial index alignment
and bounds suffice; the read value comes only from the computed raw payload. -/
theorem source_cd_uint_bind_read {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (dst : Source.Idx Γ SourceUintArrayTy)
    (src : Source.Idx Γ (.array .calldata (.int .u256) none))
    (index result : Source.Idx Γ (.int .u256)) (off len : Nat) (k : PrimTy.uint.Denote)
    (hsrc : y.1.get src=.cdRef rfl off len) (hindex : y.1.get index=sourceUint k)
    (bound : k.1.toNat<len) (cap : len<2^256) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    match sourceCalldataUintValues E F off len with
    | .error error =>
      (Source.execItems G F (fuel+6) nps none
        (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintReadInto dst index result)) .nil) :
          Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.error error,(.nil,y.2))
    | .ok vs => ∃ valid : (sourceUintValuePayload vs).length<2^256,
      let pair := hp.alloc (R := .array (.prim .uint))
        (⟨sourceUintValuePayload vs,valid⟩ : MObj H (.array (.prim .uint)))
      let ext := List.prefix_append H [RefTy.array (.prim .uint)]
      let mid : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (sourceUintValuePayload vs)⟩).1})
      ∃ value : PrimTy.uint.Denote,
        let z : Source.EMState E Γ := (mid.1.set result (sourceUint value),mid.2)
        (sourceUintValuePayload vs)[k.1.toNat]?=some value ∧
        (Source.evalE G F (fuel+4) (sourceUintCalldataBind dst src)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),mid) ∧
        (Source.evalE G F (fuel+2) (.indexArray (.local dst) (.local index) rfl)).run mid=
          (.ok (.val (sourceUint value)),mid) ∧
        (Source.evalE G F (fuel+3) (sourceUintReadInto dst index result)).run mid=(.ok (.val (sourceUint value)),z) ∧
        (Source.execItems G F (fuel+6) nps none
          (.stmt (.expr (sourceUintCalldataBind dst src)) (.stmt (.expr (sourceUintReadInto dst index result)) .nil) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
        checkedSourceFreshUints (E := E) F off len hp cap=.ok (some pair.1) ∧ Heap.Keeps ext hp pair.1 ∧
        SourceUintMemoryAt z y.2.heap.next pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
        z.1.get dst=.memRef rfl y.2.heap.next ∧ z.1.get result=sourceUint value ∧
        (∀ τ (i : Source.Idx Γ τ),dst.toNat≠i.toNat → result.toNat≠i.toNat → z.1.get i=y.1.get i) ∧
        (∀ b obj,y.2.heap.get b=some obj → z.2.heap.get b=some obj ∧ b≠y.2.heap.next) ∧
        z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
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
    let mid : Source.EMState E Γ :=
      (y.1.set dst (.memRef rfl y.2.heap.next),
        {y.2 with heap := (y.2.heap.alloc ⟨SourceUintArrayTy,sourceUintMemory (sourceUintValuePayload vs)⟩).1})
    have elements : MObj.elems .dyn (pair.1.get pair.2)=sourceUintValuePayload vs := by
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
      exact List.map_id'' (fun _ => rfl) _
    have size : pair.1.len pair.2 .dyn=len := by
      unfold Heap.len
      rw [elements,sourceCalldataUintValues_length decoded]
    have inBounds : k.1.toNat<pair.1.len pair.2 .dyn := by rw [size];exact bound
    have differentIndex : dst.toNat≠index.toNat := by
      intro same
      cases source_idx_type_of_position dst index same
    have hidx := (other (.int .u256) index differentIndex).trans hindex
    let value : PrimTy.uint.Denote := (MObj.elems .dyn (pair.1.get pair.2))[k.1.toNat]'inBounds
    have read : (Source.evalE G F (fuel+2) (.indexArray (.local dst) (.local index) rfl)).run mid=
        (.ok (.val (sourceUint value)),mid) := fresh.eval_index G F fuel dst index k selected hidx inBounds
    let z : Source.EMState E Γ := (mid.1.set result (sourceUint value),mid.2)
    have second := source_uint_read_into_of_run G F fuel mid dst index result value read
    have secondStatement := source_expr_statement_run G F (fuel+3) nps _ mid z _ second
    have finalMok : Source.MemOK E SH z :=
      ⟨⟨mok.1.1,Source.LocalsOK.set mid.1 result mok.1.2 trivial⟩,mok.2⟩
    have distinctRoot : result.toNat≠dst.toNat := by
      intro same
      cases source_idx_type_of_position result dst same
    refine ⟨value,?_,first,read,second,
      source_items_pair_run G F fuel nps _ _ y mid z firstStatement secondStatement,
      adapter,keep,fresh,finalMok,?_,source_locals_get_set _ _ _,?_,preserved,rfl,rfl,rfl,rfl⟩
    · rw [←elements]
      exact List.getElem?_eq_getElem inBounds
    · exact (source_locals_get_set_other mid.1 result dst _ distinctRoot).trans selected
    · intro τ i firstNe secondNe
      exact (source_locals_get_set_other mid.1 result i _ secondNe).trans (other τ i firstNe)

/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_bind_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cd_uint_bind_run
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.bind_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SourceUintMemoryAt.bind_memOK
/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_bind_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cd_uint_bind_copy
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.eval_read_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SourceUintMemoryAt.eval_read_bounds
/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_bind_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cd_uint_bind_low
/-- info: 'Solidity.Backend.MemoryOps.source_uint_read_into_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_uint_read_into_of_run
/-- info: 'Solidity.Backend.MemoryOps.source_cd_uint_bind_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_cd_uint_bind_read
end Solidity.Backend.MemoryOps
