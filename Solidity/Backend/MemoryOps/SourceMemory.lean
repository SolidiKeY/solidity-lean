import Solidity.Source.WellTyped
import Solidity.Backend.MemoryOps.CopyMirrorSchedule
import Solidity.Backend.MemoryOps.SnapshotProvenance

/-! Operation-side observations of the independent published source machine.
A local representation connects an existing Source memory object to an
intrinsic array. Neither interpreter is defined here. This is not a source
slice compiler, ABI decoder or physical byte-memory theorem. -/
namespace Solidity.Backend.MemoryOps

/-- Existing typed Source aggregate with bare Boolean elements. -/
def sourceBoolMemory {D : Source.Layout} (xs : List Bool) :
    Source.Data D (.array .memory .bool none) :=
  .array xs.length (fun _ h => by cases h) (fun i => .val (.bool xs[i]))

/-- Local initial representation of ONE already existing memory object. -/
def SourceBoolMemoryAt {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    (y : Source.EMState E Γ) (address : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) : Prop :=
  y.2.heap.get address=some ⟨.array .memory .bool none,sourceBoolMemory (MObj.elems a (hp.get r))⟩

theorem source_heapObj_run {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (address : Nat) (obj : Σ τ, Source.Data E.layout τ)
    (hr : y.2.heap.get address=some obj) :
    (Source.heapObj (E := E) (Γ := Γ) address).run y=(.ok obj,y) := by
  simp only [Source.heapObj,Source.Hoare.run_bind]
  rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
  simp only [hr]
  rfl

theorem source_bool_read {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (address : Nat) (xs : List Bool)
    (hr : y.2.heap.get address=some ⟨.array .memory .bool none,sourceBoolMemory xs⟩)
    (i : Nat) (hi : i<xs.length) :
    (Source.memElem (E := E) (Γ := Γ) address i .bool).run y=(.ok (.bool xs[i]),y) := by
  rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y address _ hr]
  simp only [sourceBoolMemory,hi,↓reduceDIte,Source.Data.asVal]
  rfl

theorem source_bool_bounds {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (address : Nat) (xs : List Bool)
    (hr : y.2.heap.get address=some ⟨.array .memory .bool none,sourceBoolMemory xs⟩)
    (i : Nat) (hi : xs.length≤i) :
    (Source.memElem (E := E) (Γ := Γ) address i .bool).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run y address _ hr]
  simp only [sourceBoolMemory,show ¬i<xs.length from Nat.not_lt.mpr hi,↓reduceDIte]
  rfl

/-- Complete source read vs intrinsic index correspondence, with independent
Source execution and exact source state preservation. -/
theorem SourceBoolMemoryAt.read_iff {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (F : Source.Fr) (i : PrimTy.uint.Denote) (value : Bool) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem address i.1.toNat)).run y=(.ok (.bool value),y) ↔
      hp.index r a i=some value := by
  change (Source.memElem address i.1.toNat .bool).run y=(.ok (.bool value),y) ↔
    (MObj.elems a (hp.get r))[i.1.toNat]?=some value
  by_cases hi : i.1.toNat<(MObj.elems a (hp.get r)).length
  · rw [source_bool_read y address _ hr _ hi,List.getElem?_eq_getElem hi]
    constructor
    · intro he
      exact congrArg some (Source.Val.bool.inj (Except.ok.inj (congrArg Prod.fst he)))
    · intro he
      exact congrArg (fun b : Bool => ((Except.ok (Source.Val.bool (D := E.layout) b) : Except Source.Halt (Source.Val E.layout .bool)),y)) (Option.some.inj he)
  · rw [source_bool_bounds y address _ hr _ (Nat.le_of_not_gt hi),List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    constructor <;> intro he <;> cases he

/-- Actual reached intrinsic schedule reads are related to independent Source
reads of the computed INITIAL origin. No desired final read is a premise. -/
theorem SourceBoolMemoryAt.schedule_read_iff {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (xs : List SnapshotArgs) (out : Heap H) (ho : runCaptures hp r a xs=some out)
    (F : Source.Fr) (k : Nat) (value : Bool) :
    (Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem address (captureOrigin xs k))).run y=(.ok (.bool value),y) ↔
      (MObj.elems a (out.get r))[k]?=some value := by
  rw [runCaptures_read hp out r a xs ho k]
  by_cases hi : captureOrigin xs k<(MObj.elems a (hp.get r)).length
  · rw [show (Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem address (captureOrigin xs k))).run y=
        (.ok (.bool (MObj.elems a (hp.get r))[captureOrigin xs k]),y) from source_bool_read y address _ hr _ hi,
      List.getElem?_eq_getElem hi]
    constructor
    · intro he
      exact congrArg some (Source.Val.bool.inj (Except.ok.inj (congrArg Prod.fst he)))
    · intro he
      exact congrArg (fun b : Bool => ((Except.ok (Source.Val.bool (D := E.layout) b) : Except Source.Halt (Source.Val E.layout .bool)),y)) (Option.some.inj he)
  · rw [show (Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem address (captureOrigin xs k))).run y=
        (.error (.revert (Source.panicData .index)),y) from source_bool_bounds y address _ hr _ (Nat.le_of_not_gt hi),
      List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    constructor <;> intro he <;> cases he

/-- Actual Source allocation (not a replacement allocator), with a typed
reference and the exact new heap/state; later observations use this object. -/
theorem source_bool_alloc {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (xs : List Bool) :
    (Source.allocRef (E := E) (Γ := Γ) (sourceBoolMemory xs)).run y=
      (.ok (.memRef rfl y.2.heap.next),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory .bool none,sourceBoolMemory xs⟩).1})) := by
  rfl

/-- Published MemOK preservation is consumed with all premises discharged for
this bare primitive aggregate; shape and inner conditions are structural. -/
theorem source_bool_alloc_memOK {E : Source.Env} {Γ : Source.RCtx}
    (H : Source.HeapTy) (xs : List Bool) :
    Source.Hoare (Source.MemOK E H) (Source.allocRef (E := E) (Γ := Γ) (sourceBoolMemory xs))
      (fun v y => Source.MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => Source.MemOK E H y) := by
  apply Source.Hoare.conseq (Source.allocRef_mem' (E := E) (Γ := Γ) (H := H) (sourceBoolMemory xs) (by trivial) (by change ∀ j : Fin xs.length, ∃ v, Source.Data.val (Source.Val.bool xs[j]) = Source.Data.val v; intro j; exact ⟨_,rfl⟩))
  · intro y hy
    exact ⟨hy,.array (fun i => .val trivial)⟩
  · intro v y h; exact h
  · intro h y hy; exact hy
set_option backward.isDefEq.respectTransparency false in
/-- Compose independent Source location execution with the ACTUAL published
recursive builder and reached intrinsic recaptures. Representation is INITIAL;
complete recursive target mirror and final reads are conclusions. -/
theorem SourceBoolMemoryAt.copy_schedule {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R A : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree=true) (xs : List SnapshotArgs)
    (out : Heap (sv.copyStToM hp hm).H')
    (ho : runCaptures (sv.copyStToM hp hm).heap (r.wk (sv.copyStToM hp hm).ext) a xs=some out)
    (F : Source.Fr) (k : Nat) (value : Bool) :
    sv.Mirrors out H.length (sv.copyStToM hp hm).val ∧
      ((Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem address (captureOrigin xs k))).run y=(.ok (.bool value),y) ↔
        (MObj.elems a (out.get (r.wk (sv.copyStToM hp hm).ext)))[k]?=some value) := by
  have hk : Heap.Keeps (sv.copyStToM hp hm).ext hp (sv.copyStToM hp hm).heap := SVal.keeps_copyStToM sv hm hp
  have he : MObj.elems a ((sv.copyStToM hp hm).heap.get (r.wk (sv.copyStToM hp hm).ext))=MObj.elems a (hp.get r) := by
    rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk (sv.copyStToM hp hm).ext (.prim .bool)) (fun _ => rfl)]
  have hrep : SourceBoolMemoryAt y address (sv.copyStToM hp hm).heap (r.wk (sv.copyStToM hp hm).ext) a := by
    unfold SourceBoolMemoryAt
    rw [he]
    exact hr
  exact ⟨copy_schedule_mirrors hp sv hm r a xs out ho,hrep.schedule_read_iff xs out ho F k value⟩
/-- info: 'Solidity.Backend.MemoryOps.source_bool_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_read
/-- info: 'Solidity.Backend.MemoryOps.source_bool_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.read_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.read_iff
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.schedule_read_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.schedule_read_iff
/-- info: 'Solidity.Backend.MemoryOps.source_bool_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_alloc
/-- info: 'Solidity.Backend.MemoryOps.source_bool_alloc_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_alloc_memOK
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.copy_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.copy_schedule
/-- info: 'Solidity.Backend.MemoryOps.source_heapObj_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_heapObj_run
end Solidity.Backend.MemoryOps
