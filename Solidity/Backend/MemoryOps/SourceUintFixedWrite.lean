import Solidity.Backend.MemoryOps.SourceUintFixedDefault
import Solidity.Backend.MemoryOps.SourceUintAssignment
import Solidity.Evm.MemoryObjectStatements

/-! Genuine fixed Source element mutation. Existing typed Data, Heap and Source
operations only; no dynamic cast, new evaluator or Source admission change. -/
namespace Solidity.Backend.MemoryOps

private theorem fixed_set {D : Source.Layout} {H : HTy} {n : Nat}
    (o : MObj H (.fixed (.prim .uint) n)) (i : Nat) (v : PrimTy.uint.Denote) :
    sourceUintFixedObject (D := D) (MObj.setElem .fixed o i v)=
      .array n (fun _ h => by cases h;rfl)
        (fun j => if j.val=i then .val (sourceUint v) else .val (sourceUint (o.1[j.val]'(by rw [o.2];exact j.isLt)))) := by
  unfold sourceUintFixedObject
  congr 1
  funext j
  rw [MObj.setElem_fixed]
  change Source.Data.val (sourceUint ((o.1.set i v)[j.val]'_))=_
  rw [List.getElem_set]
  by_cases hj : i=j.val
  · simp only [hj,↓reduceIte]
  · simp only [hj,Ne.symm hj,↓reduceIte]

theorem source_uint_fixed_write {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    (y : Source.EMState E Γ) (address : Nat) (o : MObj H (.fixed (.prim .uint) n))
    (hr : y.2.heap.get address=some ⟨.array .memory (.int .u256) (some n),sourceUintFixedObject o⟩)
    (i : Nat) (hi : i<n) (v : PrimTy.uint.Denote) :
    ∃ (ht : y.2.heap.ty address=some (.array .memory (.int .u256) (some n))),
      (Source.memSet (E := E) (Γ := Γ) address i (sourceUint v)).run y=
        (.ok (), (y.1,{y.2 with heap := y.2.heap.write address (sourceUintFixedObject (MObj.setElem .fixed o i v)) ht})) := by
  have ht : y.2.heap.ty address=some (.array .memory (.int .u256) (some n)) := by
    change (y.2.heap.get address).map Sigma.fst=some _
    rw [hr];rfl
  refine ⟨ht,?_⟩
  have hh : (Source.heapObj (E := E) (Γ := Γ) address).run y=
      (.ok ⟨.array .memory (.int .u256) (some n),sourceUintFixedObject o⟩,y) := by
    simp only [Source.heapObj,Source.Hoare.run_bind]
    rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
    simp only [hr]
    rfl
  rw [Source.memSet,Source.Hoare.run_bind,hh]
  simp only [sourceUintFixedObject,hi,↓reduceDIte]
  rw [←fixed_set o i v]
  simp only [Source.heapPut,Source.Hoare.run_bind]
  rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
  simp only [ht,↓reduceDIte]
  rfl

theorem SourceUintFixedAt.write_addr {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) n)}
    (hr : SourceUintFixedAt y address hp r) (F : Source.Fr) (fuel : Nat)
    (i v : PrimTy.uint.Denote) (hi : i.1.toNat<n) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r .fixed i) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.1.toNat) (sourceUint v)).run y=(.ok (),z) ∧
      SourceUintFixedAt z address out r := by
  obtain ⟨ht,hw⟩ := source_uint_fixed_write y address (hp.get r) hr i.1.toNat hi v
  let out := hp.set r (MObj.setElem .fixed (hp.get r) i.1.toNat v)
  let z : Source.EMState E Γ := (y.1,{y.2 with heap := y.2.heap.write address (sourceUintFixedObject (MObj.setElem .fixed (hp.get r) i.1.toNat v)) ht})
  refine ⟨out,z,?_,hw,?_⟩
  · have hlen : (MObj.elems .fixed (hp.get r)).length=n := by simpa only [MObj.elems_fixed] using (hp.get r).2
    simp only [Heap.writeAddr,Heap.setIndex,hlen,hi,↓reduceIte]
    rfl
  · unfold SourceUintFixedAt
    change (y.2.heap.write address _ ht).get address=some _
    rw [Source.Heap.write_get,Heap.get_set_same]

theorem SourceUintFixedAt.write_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) n)}
    (hr : SourceUintFixedAt y address hp r) (F : Source.Fr) (fuel : Nat)
    (i v : PrimTy.uint.Denote) (hi : n≤i.1.toNat) :
    (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.1.toNat) (sourceUint v)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧ hp.writeAddr (.index r .fixed i) v=none := by
  have hh : (Source.heapObj (E := E) (Γ := Γ) address).run y=
      (.ok ⟨.array .memory (.int .u256) (some n),sourceUintFixedObject (hp.get r)⟩,y) := by
    simp only [Source.heapObj,Source.Hoare.run_bind]
    rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
    change (match y.2.heap.get address with | some x => pure x | none => Source.EM.halt (.stuck "dangling memory reference")).run y=_
    rw [hr]
    rfl
  refine ⟨?_,?_⟩
  · change (Source.memSet address i.1.toNat (sourceUint v)).run y=_
    rw [Source.memSet,Source.Hoare.run_bind,hh]
    simp only [sourceUintFixedObject,show ¬i.1.toNat<n from Nat.not_lt.mpr hi,↓reduceDIte]
    rfl
  · have hlen : (MObj.elems .fixed (hp.get r)).length=n := by simpa only [MObj.elems_fixed] using (hp.get r).2
    simp only [Heap.writeAddr,Heap.setIndex,hlen,show ¬i.1.toNat<n from Nat.not_lt.mpr hi,↓reduceIte]


theorem SourceUintFixedAt.write_frames {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y z : Source.EMState E Γ} {address : Nat} {hp out : Heap H} {r : HRef H (.fixed (.prim .uint) n)}
    (hr : SourceUintFixedAt y address hp r) (F : Source.Fr) (fuel : Nat)
    (i v : PrimTy.uint.Denote) (hi : i.1.toNat<n)
    (hw : hp.writeAddr (.index r .fixed i) v=some out)
    (hs : (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem address i.1.toNat) (sourceUint v)).run y=(.ok (),z)) :
    z.1=y.1 ∧
    (∀ {Q : RefTy} (q : HRef H Q),r.id≠q.id → out.get q=hp.get q) ∧
    (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
    z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  obtain ⟨ht,hknown⟩ := source_uint_fixed_write y address (hp.get r) hr i.1.toNat hi v
  have hz := congrArg Prod.snd (hs.symm.trans hknown)
  dsimp only at hz
  subst z
  refine ⟨rfl,fun q hn => indexedWrite_frame hp out r .fixed i v hw q hn,?_,rfl,rfl,rfl,rfl⟩
  intro b hn
  exact Source.Heap.write_other y.2.heap hn _ ht

/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_write
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.write_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.write_addr
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.write_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.write_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.write_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.write_frames
end Solidity.Backend.MemoryOps
