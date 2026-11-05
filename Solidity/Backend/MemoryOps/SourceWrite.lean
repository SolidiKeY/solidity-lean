import Solidity.Backend.MemoryOps.SourceMemory

/-! Independent Source location writes and existing intrinsic singleton copies.
Only existing typed operations are composed; Option rejection and Source halt
remain distinct observations. No emitted loop or byte-memory semantics. -/
namespace Solidity.Backend.MemoryOps

private theorem boolArray_congr {D : Source.Layout} {n m : Nat}
    (hn : ∀ k, none=some k → k=n) (hm : ∀ k, none=some k → k=m)
    (f : Fin n → Source.Data D .bool) (g : Fin m → Source.Data D .bool)
    (hl : n=m) (he : ∀ j : Fin n, f j=g ⟨j.val,by omega⟩) :
    Source.Data.array (l := .memory) (n := none) n hn f=Source.Data.array (l := .memory) (n := none) m hm g := by
  subst m
  have hf : f=g := funext he
  cases hf
  rfl

private theorem sourceBoolMemory_set {D : Source.Layout} (xs : List Bool) (i : Nat) (v : Bool) :
    sourceBoolMemory (D := D) (xs.set i v) =
      .array xs.length (fun _ h => by cases h)
        (fun j => if j.val=i then .val (.bool v) else .val (.bool xs[j])) := by
  apply boolArray_congr _ _ _ _ (List.length_set ..)
  intro j
  change Source.Data.val (Source.Val.bool ((xs.set i v)[j.val])) =
    if j.val=i then .val (.bool v) else .val (.bool xs[j.val])
  rw [List.getElem_set]
  by_cases hj : i=j.val
  · simp only [hj,↓reduceIte]
  · simp only [hj,Ne.symm hj,↓reduceIte]

theorem source_bool_write {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (address : Nat) (xs : List Bool)
    (hr : y.2.heap.get address=some ⟨.array .memory .bool none,sourceBoolMemory xs⟩)
    (i : Nat) (hi : i<xs.length) (v : Bool) :
    ∃ (ht : y.2.heap.ty address=some (.array .memory .bool none)),
      (Source.memSet (E := E) (Γ := Γ) address i (.bool v)).run y=
        (.ok (), (y.1,{y.2 with heap := y.2.heap.write address (sourceBoolMemory (xs.set i v)) ht})) := by
  have ht : y.2.heap.ty address=some (.array .memory .bool none) := by
    change (y.2.heap.get address).map Sigma.fst=some _
    rw [hr]; rfl
  refine ⟨ht,?_⟩
  have hh : (Source.heapObj (E := E) (Γ := Γ) address).run y=
      (.ok ⟨.array .memory .bool none,sourceBoolMemory xs⟩,y) := by
    simp only [Source.heapObj,Source.Hoare.run_bind]
    rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
    simp only [hr]
    rfl
  rw [Source.memSet,Source.Hoare.run_bind,hh]
  simp only [sourceBoolMemory,hi,↓reduceDIte]
  rw [←sourceBoolMemory_set xs i v]
  simp only [Source.heapPut,Source.Hoare.run_bind]
  rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
  simp only [ht,↓reduceDIte]
  rfl

private theorem replaceSlice_singleton {α : Type} (xs : List α) (d : Nat) (v : α)
    (hd : d<xs.length) : replaceSlice xs d [v]=xs.set d v := by
  apply List.ext_getElem?
  intro i
  rw [replaceSlice_read_cases xs [v] d i (by simp only [List.length_singleton]; omega)]
  by_cases he : i=d
  · subst i
    simp only [List.length_singleton, Nat.le_refl, Nat.lt_succ_self, and_self,↓reduceIte,
      Nat.sub_self,List.getElem?_cons_zero,List.getElem?_set_self hd]
  · have hn : ¬(d≤i ∧ i<d+[v].length) := by simp only [List.length_singleton]; omega
    rw [if_neg hn,List.getElem?_set_ne (Ne.symm he)]

theorem capture_singleton_elems {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (src dst : Nat)
    (hs : src<hp.len r a) (hd : dst<hp.len r a) :
    MObj.elems a ((captureOverwrite hp r a r a src (src+1) dst
      ⟨by omega,by omega⟩ (by omega)).get r)=
      (MObj.elems a (hp.get r)).set dst (MObj.elems a (hp.get r))[src] := by
  unfold captureOverwrite
  rw [overwriteSlice_elems]
  have hpayload : sliceElems hp r a src (src+1)=[(MObj.elems a (hp.get r))[src]] := by
    unfold sliceElems
    rw [List.drop_eq_getElem_cons hs]
    simp only [Nat.add_sub_cancel_left,List.take_succ_cons,List.take_zero]
  rw [hpayload]
  exact replaceSlice_singleton _ _ _ hd

/-- Ordinary composition of the two EXISTING independent Source operations.
The read executes before the write, including when the locations alias. -/
def sourceBoolCopy {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (fuel address src dst : Nat) : Source.EM E Γ Unit := do
  let value ← Source.readLoc F (τ := .bool) (.mem address src)
  Source.writeLoc F fuel (.mem address dst) value

theorem SourceBoolMemoryAt.copy {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (F : Source.Fr) (fuel src dst : Nat) (hs : src<hp.len r a) (hd : dst<hp.len r a) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      checkedCaptureOverwrite hp r a r a src (src+1) dst=some out ∧
      (sourceBoolCopy (E := E) (Γ := Γ) F fuel address src dst).run y=(.ok (),z) ∧
      SourceBoolMemoryAt z address out r a := by
  let values := MObj.elems a (hp.get r)
  obtain ⟨ht,hw⟩ := source_bool_write y address values hr dst hd values[src]
  let z : Source.EMState E Γ :=
    (y.1,{y.2 with heap := y.2.heap.write address (sourceBoolMemory (values.set dst values[src])) ht})
  let out := captureOverwrite hp r a r a src (src+1) dst ⟨by omega,by omega⟩ (by omega)
  refine ⟨out,z,checkedCaptureOverwrite_some hp r a r a src (src+1) dst _ _,?_,?_⟩
  · rw [sourceBoolCopy,Source.Hoare.run_bind,show
      (Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem address src)).run y=
      (.ok (.bool values[src]),y) from source_bool_read y address values hr src hs]
    exact hw
  · unfold SourceBoolMemoryAt
    change (y.2.heap.write address (sourceBoolMemory (values.set dst values[src])) ht).get address=some _
    rw [Source.Heap.write_get,capture_singleton_elems hp r a src dst hs hd]

/-- Actual published preservation, used after the read has returned without
changing state. No postcondition or final MemOK is assumed. -/
theorem SourceBoolMemoryAt.copy_memOK {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y z : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (F : Source.Fr) (fuel src dst : Nat) (hs : src<hp.len r a)
    (h : (sourceBoolCopy (E := E) (Γ := Γ) F fuel address src dst).run y=(.ok (),z))
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) : Source.MemOK E SH z := by
  rw [sourceBoolCopy,Source.Hoare.run_bind,show
      (Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem address src)).run y=
      (.ok (.bool (MObj.elems a (hp.get r))[src]),y) from source_bool_read y address _ hr src hs] at h
  have hpres := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F fuel
    (.mem (τ := .bool) address dst) (.bool (MObj.elems a (hp.get r))[src]) y ⟨hm,by trivial⟩
  change (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address dst)
    (.bool (MObj.elems a (hp.get r))[src])).run y=(.ok (),z) at h
  rw [h] at hpres
  exact hpres

theorem source_bool_write_bounds {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (address : Nat) (xs : List Bool)
    (hr : y.2.heap.get address=some ⟨.array .memory .bool none,sourceBoolMemory xs⟩)
    (i : Nat) (hi : xs.length≤i) (v : Bool) :
    (Source.memSet (E := E) (Γ := Γ) address i (.bool v)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  have hh : (Source.heapObj (E := E) (Γ := Γ) address).run y=
      (.ok ⟨.array .memory .bool none,sourceBoolMemory xs⟩,y) := by
    simp only [Source.heapObj,Source.Hoare.run_bind]
    rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
    simp only [hr]
    rfl
  rw [Source.memSet,Source.Hoare.run_bind,hh]
  simp only [sourceBoolMemory,show ¬i<xs.length from Nat.not_lt.mpr hi,↓reduceDIte]
  rfl

/-- The first bad read short-circuits; a bad write is reached only after a
successful unchanged-state read. Both exact outcomes are derived separately
from Option rejection, not identified with its semantics. -/
theorem SourceBoolMemoryAt.copy_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (F : Source.Fr) (fuel src dst : Nat) (hb : hp.len r a≤src ∨ hp.len r a≤dst) :
    (sourceBoolCopy (E := E) (Γ := Γ) F fuel address src dst).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    checkedCaptureOverwrite hp r a r a src (src+1) dst=none := by
  constructor
  · by_cases hs : src<hp.len r a
    · have hd : hp.len r a≤dst := by omega
      rw [sourceBoolCopy,Source.Hoare.run_bind,show
        (Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem address src)).run y=
        (.ok (.bool (MObj.elems a (hp.get r))[src]),y) from source_bool_read y address _ hr src hs]
      exact source_bool_write_bounds y address _ hr dst hd _
    · rw [sourceBoolCopy,Source.Hoare.run_bind,show
        (Source.readLoc (E := E) (Γ := Γ) F (τ := .bool) (.mem address src)).run y=
        (.error (.revert (Source.panicData .index)),y) from source_bool_bounds y address _ hr src (Nat.le_of_not_gt hs)]
  · rw [checkedCaptureOverwrite_none_iff]
    omega

/-- info: 'Solidity.Backend.MemoryOps.source_bool_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_write
/-- info: 'Solidity.Backend.MemoryOps.capture_singleton_elems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_singleton_elems
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.copy
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.copy_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.copy_memOK
/-- info: 'Solidity.Backend.MemoryOps.source_bool_write_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_write_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.copy_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.copy_bounds
end Solidity.Backend.MemoryOps
