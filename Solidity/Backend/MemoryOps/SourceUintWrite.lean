import Solidity.Backend.MemoryOps.SourceUintMemory
import Solidity.Backend.MemoryOps.SourceSequence

/-! Actual numeric Source memSet/writeLoc and intrinsic address updates.
Existing operators only, all canonical uint256 values, no new semantics or
profile restriction. The initial local observer derives the reached observer. -/
namespace Solidity.Backend.MemoryOps

private theorem uintArray_congr {D : Source.Layout} {n m : Nat}
    (hn : ∀ k, none=some k → k=n) (hm : ∀ k, none=some k → k=m)
    (f : Fin n → Source.Data D (.int .u256)) (g : Fin m → Source.Data D (.int .u256))
    (hl : n=m) (he : ∀ j : Fin n, f j=g ⟨j.val,by omega⟩) :
    Source.Data.array (l := .memory) (n := none) n hn f=Source.Data.array (l := .memory) (n := none) m hm g := by
  subst m
  have hf : f=g := funext he
  cases hf
  rfl

private theorem sourceUintMemory_set {D : Source.Layout} (xs : List PrimTy.uint.Denote) (i : Nat) (v : PrimTy.uint.Denote) :
    sourceUintMemory (D := D) (xs.set i v) =
      .array xs.length (fun _ h => by cases h)
        (fun j => if j.val=i then .val (sourceUint v) else .val (sourceUint xs[j])) := by
  apply uintArray_congr _ _ _ _ (List.length_set ..)
  intro j
  change Source.Data.val (sourceUint ((xs.set i v)[j.val])) =
    if j.val=i then .val (sourceUint v) else .val (sourceUint xs[j.val])
  rw [List.getElem_set]
  by_cases hj : i=j.val
  · simp only [hj,↓reduceIte]
  · simp only [hj,Ne.symm hj,↓reduceIte]

theorem source_uint_write {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (address : Nat) (xs : List PrimTy.uint.Denote)
    (hr : y.2.heap.get address=some ⟨.array .memory (.int .u256) none,sourceUintMemory xs⟩)
    (i : Nat) (hi : i<xs.length) (v : PrimTy.uint.Denote) :
    ∃ (ht : y.2.heap.ty address=some (.array .memory (.int .u256) none)),
      (Source.memSet (E := E) (Γ := Γ) address i (sourceUint v)).run y=
        (.ok (), (y.1,{y.2 with heap := y.2.heap.write address (sourceUintMemory (xs.set i v)) ht})) := by
  have ht : y.2.heap.ty address=some (.array .memory (.int .u256) none) := by
    change (y.2.heap.get address).map Sigma.fst=some _
    rw [hr]; rfl
  refine ⟨ht,?_⟩
  have hh : (Source.heapObj (E := E) (Γ := Γ) address).run y=
      (.ok ⟨.array .memory (.int .u256) none,sourceUintMemory xs⟩,y) := by
    simp only [Source.heapObj,Source.Hoare.run_bind]
    rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
    simp only [hr]
    rfl
  rw [Source.memSet,Source.Hoare.run_bind,hh]
  simp only [sourceUintMemory,hi,↓reduceDIte]
  rw [←sourceUintMemory_set xs i v]
  simp only [Source.heapPut,Source.Hoare.run_bind]
  rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
  simp only [ht,↓reduceDIte]
  rfl

theorem SourceUintMemoryAt.write_addr {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (v : PrimTy.uint.Denote)
    (hi : i.1.toNat<hp.len r a) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r a i) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.1.toNat) (sourceUint v)).run y=(.ok (),z) ∧
      SourceUintMemoryAt z address out r a := by
  let values := MObj.elems a (hp.get r)
  obtain ⟨ht,hw⟩ := source_uint_write y address values hr i.1.toNat hi v
  let out := hp.set r (MObj.setElem a (hp.get r) i.1.toNat v)
  let z : Source.EMState E Γ :=
    (y.1,{y.2 with heap := y.2.heap.write address (sourceUintMemory (values.set i.1.toNat v)) ht})
  refine ⟨out,z,?_,hw,?_⟩
  · simp only [Heap.len] at hi
    simp only [Heap.writeAddr,Heap.setIndex,hi,↓reduceIte]
    rfl
  · unfold SourceUintMemoryAt
    change (y.2.heap.write address (sourceUintMemory (values.set i.1.toNat v)) ht).get address=some _
    rw [Source.Heap.write_get,Heap.get_set_same,MObj.elems_setElem]

theorem source_uint_write_bounds {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (address : Nat) (xs : List PrimTy.uint.Denote)
    (hr : y.2.heap.get address=some ⟨.array .memory (.int .u256) none,sourceUintMemory xs⟩)
    (i : Nat) (hi : xs.length≤i) (v : PrimTy.uint.Denote) :
    (Source.memSet (E := E) (Γ := Γ) address i (sourceUint v)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  have hh : (Source.heapObj (E := E) (Γ := Γ) address).run y=
      (.ok ⟨.array .memory (.int .u256) none,sourceUintMemory xs⟩,y) := by
    simp only [Source.heapObj,Source.Hoare.run_bind]
    rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
    simp only [hr]
    rfl
  rw [Source.memSet,Source.Hoare.run_bind,hh]
  simp only [sourceUintMemory,show ¬i<xs.length from Nat.not_lt.mpr hi,↓reduceDIte]
  rfl


/-- Actual write outcomes give the local/other-object/world frames. Independent
Source-address and typed-identity separation are local sufficient cases, not a
global address injection hypothesis or a restriction on admitted aliases. -/
theorem SourceUintMemoryAt.write_frames {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y z : Source.EMState E Γ} {address : Nat} {hp out : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (F : Source.Fr) (fuel : Nat) (i v : PrimTy.uint.Denote) (hi : i.1.toNat<hp.len r a)
    (hw : hp.writeAddr (.index r a i) v=some out)
    (hs : (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.1.toNat) (sourceUint v)).run y=(.ok (),z)) :
    z.1=y.1 ∧
    (∀ {Q : RefTy} (q : HRef H Q),r.id≠q.id → out.get q=hp.get q) ∧
    (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
    (∀ {Q : RefTy} (q : HRef H Q) (aq : ArrTy Q (.prim .uint)) (b : Nat),
      r.id≠q.id → b≠address → SourceUintMemoryAt y b hp q aq → SourceUintMemoryAt z b out q aq) ∧
    z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  obtain ⟨ht,hknown⟩ := source_uint_write y address _ hr i.1.toNat hi v
  have hz := congrArg Prod.snd (hs.symm.trans hknown)
  dsimp only at hz
  subst z
  have hq : ∀ {Q : RefTy} (q : HRef H Q),r.id≠q.id → out.get q=hp.get q :=
    fun q hn => indexedWrite_frame hp out r a i v hw q hn
  have hb : ∀ b,b≠address → (y.2.heap.write address (sourceUintMemory ((MObj.elems a (hp.get r)).set i.1.toNat v)) ht).get b=y.2.heap.get b := by
    intro b hn
    exact Source.Heap.write_other y.2.heap hn _ ht
  refine ⟨rfl,hq,hb,?_,rfl,rfl,rfl,rfl⟩
  intro Q q aq b hne haddr hrep
  unfold SourceUintMemoryAt at hrep ⊢
  rw [hb b haddr,hq q hne]
  exact hrep

/-- info: 'Solidity.Backend.MemoryOps.source_uint_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_write
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.write_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.write_addr
/-- info: 'Solidity.Backend.MemoryOps.source_uint_write_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_write_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.write_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.write_frames
end Solidity.Backend.MemoryOps
