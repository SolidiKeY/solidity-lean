import Solidity.Backend.MemoryOps.SourceWrite

/-! Existing independent Source delete and actual intrinsic memory-address clear.
Primitive Boolean case only. Source fuel timeout and index panic are distinct;
no emitted target or source-profile change. -/
namespace Solidity.Backend.MemoryOps

theorem SourceBoolMemoryAt.write_addr {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (v : Bool)
    (hi : i.1.toNat<hp.len r a) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r a i) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.1.toNat) (.bool v)).run y=(.ok (),z) ∧
      SourceBoolMemoryAt z address out r a := by
  let values := MObj.elems a (hp.get r)
  obtain ⟨ht,hw⟩ := source_bool_write y address values hr i.1.toNat hi v
  let out := hp.set r (MObj.setElem a (hp.get r) i.1.toNat v)
  let z : Source.EMState E Γ :=
    (y.1,{y.2 with heap := y.2.heap.write address (sourceBoolMemory (values.set i.1.toNat v)) ht})
  refine ⟨out,z,?_,hw,?_⟩
  · simp only [Heap.len] at hi
    simp only [Heap.writeAddr,Heap.setIndex,hi,↓reduceIte]
    rfl
  · unfold SourceBoolMemoryAt
    change (y.2.heap.write address (sourceBoolMemory (values.set i.1.toNat v)) ht).get address=some _
    rw [Source.Heap.write_get,Heap.get_set_same,MObj.elems_setElem]

/-- Positive existing Source fuel obtains its actual primitive default; the
intrinsic address write uses PrimTy.dflt, not a supplied replacement payload. -/
theorem SourceBoolMemoryAt.delete_addr {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (hi : i.1.toNat<hp.len r a) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r a i) (PrimTy.dflt .bool)=some out ∧
      (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+1) (τ := .bool) (.mem address i.1.toNat)).run y=(.ok (),z) ∧
      SourceBoolMemoryAt z address out r a := by
  obtain ⟨out,z,ho,hz,hr'⟩ := hr.write_addr F (fuel+1) i false hi
  refine ⟨out,z,ho,?_,hr'⟩
  exact hz

/-- Actual intrinsic clearT execution, not just an arbitrary postrelation. -/
theorem SourceBoolMemoryAt.clearT {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (σ : State C Δ) {R : RefTy}
    (r : HRef σ.H R) (a : ArrTy R (.prim .bool))
    (hr : SourceBoolMemoryAt y address σ.heap r a)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (hi : i.1.toNat<σ.heap.len r a) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ),
      σ.heap.writeAddr (.index r a i) (PrimTy.dflt .bool)=some out ∧
      TRun.clearT σ (.index r a i) rfl=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+1) (τ := .bool) (.mem address i.1.toNat)).run y=(.ok (),z) ∧
      SourceBoolMemoryAt z address out r a := by
  obtain ⟨out,z,ho,hz,hr'⟩ := hr.delete_addr F fuel i hi
  refine ⟨out,z,ho,?_,hz,hr'⟩
  simp only [TRun.clearT,ho,TRes.ofOpt]
  rfl

theorem source_bool_delete_timeout {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (F : Source.Fr) (address i : Nat) :
    (Source.deleteLoc (E := E) (Γ := Γ) F 0 (τ := .bool) (.mem address i)).run y=(.error .timeout,y) := by
  rfl

theorem SourceBoolMemoryAt.delete_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (hi : hp.len r a≤i.1.toNat) :
    (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+1) (τ := .bool) (.mem address i.1.toNat)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
      hp.writeAddr (.index r a i) (PrimTy.dflt .bool)=none := by
  constructor
  · exact source_bool_write_bounds y address _ hr i.1.toNat hi false
  · simp only [Heap.len] at hi
    simp only [Heap.writeAddr,Heap.setIndex,show ¬i.1.toNat<(MObj.elems a (hp.get r)).length from Nat.not_lt.mpr hi,↓reduceIte]

/-- Consume the published delete invariant on the actual reached Source state. -/
theorem source_bool_delete_memOK {E : Source.Env} {Γ : Source.RCtx}
    (y z : Source.EMState E Γ) (SH : Source.HeapTy) (hm : Source.MemOK E SH y)
    (F : Source.Fr) (fuel address i : Nat)
    (hz : (Source.deleteLoc (E := E) (Γ := Γ) F fuel (τ := .bool) (.mem address i)).run y=(.ok (),z)) :
    Source.MemOK E SH z := by
  have h := Source.deleteLoc_memOK (E := E) (Γ := Γ) (H := SH) F fuel (.mem (τ := .bool) address i) y hm
  rw [hz] at h
  exact h

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.write_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.write_addr
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.delete_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.delete_addr
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.clearT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.clearT
/-- info: 'Solidity.Backend.MemoryOps.source_bool_delete_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_delete_timeout
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.delete_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.delete_bounds
/-- info: 'Solidity.Backend.MemoryOps.source_bool_delete_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_bool_delete_memOK
end Solidity.Backend.MemoryOps
