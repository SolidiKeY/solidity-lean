import Solidity.Backend.MemoryOps.SourceMemory
import Solidity.Backend.MemoryOps.SourceIndexedDelete
import Solidity.Backend.MemoryOps.CalldataUintTransfer

/-! Existing Source memory uint256 arrays observed against intrinsic typed arrays.
The exact published value conversion is reused. No decoder, heap semantics or
Source copy operation is introduced; schedule observations read INITIAL Source. -/
namespace Solidity.Backend.MemoryOps

def sourceUintMemory {D : Source.Layout} (xs : List PrimTy.uint.Denote) :
    Source.Data D (.array .memory (.int .u256) none) :=
  .array xs.length (fun _ h => by cases h) (fun i => .val (sourceUint xs[i]))

/-- INITIAL one-object correspondence; the Source object has dynamic array type.
The intrinsic observation may use either published dynamic or fixed ArrTy. -/
def SourceUintMemoryAt {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    (y : Source.EMState E Γ) (address : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .uint)) : Prop :=
  y.2.heap.get address=some ⟨.array .memory (.int .u256) none,sourceUintMemory (MObj.elems a (hp.get r))⟩

theorem source_uint_read {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (address : Nat) (xs : List PrimTy.uint.Denote)
    (hr : y.2.heap.get address=some ⟨.array .memory (.int .u256) none,sourceUintMemory xs⟩)
    (i : Nat) (hi : i<xs.length) :
    (Source.memElem (E := E) (Γ := Γ) address i (.int .u256)).run y=(.ok (sourceUint xs[i]),y) := by
  rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y address _ hr]
  simp only [sourceUintMemory,hi,↓reduceDIte,Source.Data.asVal]
  rfl

theorem source_uint_bounds {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (address : Nat) (xs : List PrimTy.uint.Denote)
    (hr : y.2.heap.get address=some ⟨.array .memory (.int .u256) none,sourceUintMemory xs⟩)
    (i : Nat) (hi : xs.length≤i) :
    (Source.memElem (E := E) (Γ := Γ) address i (.int .u256)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y address _ hr]
  simp only [sourceUintMemory,show ¬i<xs.length from Nat.not_lt.mpr hi,↓reduceDIte]
  rfl

/-- Complete read equivalence uses the actual exact uint conversion, never an
assumed payload agreement or truncation. Natural indices have no added cap. -/
theorem SourceUintMemoryAt.read_nat_iff {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (F : Source.Fr) (i : Nat) (value : PrimTy.uint.Denote) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .int .u256) (.mem address i)).run y=(.ok (sourceUint value),y) ↔
      (MObj.elems a (hp.get r))[i]?=some value := by
  change (Source.memElem address i (.int .u256)).run y=(.ok (sourceUint value),y) ↔ _
  by_cases hi : i<(MObj.elems a (hp.get r)).length
  · rw [source_uint_read y address _ hr _ hi,List.getElem?_eq_getElem hi]
    constructor
    · intro he
      have hv := congrArg (fun v : Source.Val E.layout (.int .u256) => calldataUint (.val v))
        (Except.ok.inj (congrArg Prod.fst he))
      have hv' : (MObj.elems a (hp.get r))[i]=value := by
        simpa only [calldataUint_sourceUint] using hv
      exact congrArg some hv'
    · intro he
      exact congrArg (fun v : PrimTy.uint.Denote => ((Except.ok (sourceUint (D := E.layout) v) : Except Source.Halt (Source.Val E.layout (.int .u256))),y)) (Option.some.inj he)
  · rw [source_uint_bounds y address _ hr _ (Nat.le_of_not_gt hi),List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    constructor <;> intro he <;> cases he

theorem SourceUintMemoryAt.read_iff {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (F : Source.Fr) (i value : PrimTy.uint.Denote) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .int .u256) (.mem address i.1.toNat)).run y=(.ok (sourceUint value),y) ↔
      hp.index r a i=some value := hr.read_nat_iff F i.1.toNat value

/-- Reached memory recaptures use computed INITIAL Source read provenance.
This does not assert that a Source copy loop or unchanged-index final observer ran. -/
theorem SourceUintMemoryAt.schedule_read_iff {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (xs : List SnapshotArgs) (out : Heap H) (ho : runCaptures hp r a xs=some out)
    (F : Source.Fr) (k : Nat) (value : PrimTy.uint.Denote) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .int .u256) (.mem address (captureOrigin xs k))).run y=(.ok (sourceUint value),y) ↔
      (MObj.elems a (out.get r))[k]?=some value := by
  rw [runCaptures_read hp out r a xs ho k]
  exact hr.read_nat_iff F (captureOrigin xs k) value

theorem SourceUintMemoryAt.keeps {E : Source.Env} {Γ : Source.RCtx} {H K : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {hq : Heap K} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (ext : H.IsPrefix K) (hk : Heap.Keeps ext hp hq) :
    SourceUintMemoryAt y address hq (r.wk ext) a := by
  unfold SourceUintMemoryAt at hr ⊢
  rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk ext (.prim .uint)) (fun _ => rfl)]
  exact hr

/-- Actual published recursive storage-tree builder followed by an arbitrary
successful old-root schedule: recursive copied mirror and numeric Source read
provenance derive together. mapFree and actual Some execution remain explicit. -/
theorem SourceUintMemoryAt.copy_schedule {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R A : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree=true) (xs : List SnapshotArgs)
    (out : Heap (sv.copyStToM hp hm).H')
    (ho : runCaptures (sv.copyStToM hp hm).heap (r.wk (sv.copyStToM hp hm).ext) a xs=some out)
    (F : Source.Fr) (k : Nat) (value : PrimTy.uint.Denote) :
    sv.Mirrors out H.length (sv.copyStToM hp hm).val ∧
      ((Source.readLoc (E := E) (Γ := Γ) F (τ := .int .u256) (.mem address (captureOrigin xs k))).run y=(.ok (sourceUint value),y) ↔
        (MObj.elems a (out.get (r.wk (sv.copyStToM hp hm).ext)))[k]?=some value) := by
  have hk : Heap.Keeps (sv.copyStToM hp hm).ext hp (sv.copyStToM hp hm).heap := SVal.keeps_copyStToM sv hm hp
  exact ⟨copy_schedule_mirrors hp sv hm r a xs out ho,
    (hr.keeps (sv.copyStToM hp hm).ext hk).schedule_read_iff xs out ho F k value⟩

/-- Published allocator execution provides inhabited INITIAL objects; this is
not a Source new-expression or an emitted allocator implementation. -/
theorem source_uint_alloc {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (xs : List PrimTy.uint.Denote) :
    (Source.allocRef (E := E) (Γ := Γ) (sourceUintMemory xs)).run y=
      (.ok (.memRef rfl y.2.heap.next),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) none,sourceUintMemory xs⟩).1})) := by
  rfl

theorem source_uint_alloc_memOK {E : Source.Env} {Γ : Source.RCtx}
    (H : Source.HeapTy) (xs : List PrimTy.uint.Denote) :
    Source.Hoare (Source.MemOK E H) (Source.allocRef (E := E) (Γ := Γ) (sourceUintMemory xs))
      (fun v y => Source.MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => Source.MemOK E H y) := by
  apply Source.Hoare.conseq (Source.allocRef_mem' (E := E) (Γ := Γ) (H := H) (sourceUintMemory xs) (by trivial)
    (by change ∀ j : Fin xs.length, ∃ v, Source.Data.val (sourceUint xs[j]) = Source.Data.val v; intro j; exact ⟨_,rfl⟩))
  · intro y hy
    exact ⟨hy,.array (fun i => .val trivial)⟩
  · intro v y h;exact h
  · intro h y hy;exact hy

theorem SourceUintMemoryAt.length_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a) (F : Source.Fr) :
    (Source.lengthOf (E := E) (Γ := Γ) F
      (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) none))).run y=(.ok (hp.len r a),y) := by
  simp only [Source.lengthOf,Source.Hoare.run_bind,Heap.len]
  rw [source_heapObj_run y address _ hr]
  rfl

theorem SourceUintMemoryAt.indexLoc_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (F : Source.Fr) (k : Nat) (hk : k<hp.len r a) :
    (Source.indexLoc (E := E) (Γ := Γ) F
      (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) none)) k).run y=(.ok (.mem address k),y) := by
  rw [Source.indexLoc,Source.Hoare.run_bind,hr.length_run F]
  simp only [hk,↓reduceIte]
  rfl

theorem SourceUintMemoryAt.indexLoc_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (F : Source.Fr) (k : Nat) (hk : hp.len r a≤k) :
    (Source.indexLoc (E := E) (Γ := Γ) F
      (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) none)) k).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.indexLoc,Source.Hoare.run_bind,hr.length_run F]
  simp only [show ¬k<hp.len r a from Nat.not_lt.mpr hk,↓reduceIte]
  rfl

/-- Actual resolved syntax read from INITIAL array and local alignment. No
computed Source location, successful read or desired output is a premise. -/
theorem SourceUintMemoryAt.eval_index {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) none)) (i : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hi : y.1.get i=sourceUint k) (hk : k.1.toNat<hp.len r a) :
    (Source.evalE G F (n+2) (.indexArray (.local root) (.local i) rfl)).run y=
      (.ok (.val (sourceUint ((MObj.elems a (hp.get r))[k.1.toNat]'hk))),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F n y root _ hroot]
  change ((Source.evalE G F (n+1) (.local i)) >>= fun v => Source.indexNat v >>= fun k =>
    Source.indexLoc F (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) none)) k >>=
      fun loc => Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F n y i _ hi]
  change (Source.indexLoc F (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) none)) k.1.toNat >>=
    fun loc => Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.indexLoc_run F _ hk]
  change (Source.readLoc F (τ := .int .u256) (.mem address k.1.toNat) >>= fun v => pure (Source.RVal.val v)).run y=_
  have hread : (Source.readLoc (E := E) (Γ := Γ) F (τ := .int .u256) (.mem address k.1.toNat)).run y=
      (.ok (sourceUint ((MObj.elems a (hp.get r))[k.1.toNat]'hk)),y) := source_uint_read y address _ hr _ hk
  rw [Source.Hoare.run_bind,hread]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.source_uint_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_read
/-- info: 'Solidity.Backend.MemoryOps.source_uint_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.read_nat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.read_nat_iff
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.read_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.read_iff
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.schedule_read_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.schedule_read_iff
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.keeps
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.copy_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.copy_schedule
/-- info: 'Solidity.Backend.MemoryOps.source_uint_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_alloc
/-- info: 'Solidity.Backend.MemoryOps.source_uint_alloc_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_alloc_memOK
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.length_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.length_run
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.indexLoc_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.indexLoc_run
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.indexLoc_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.indexLoc_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.eval_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.eval_index
end Solidity.Backend.MemoryOps
