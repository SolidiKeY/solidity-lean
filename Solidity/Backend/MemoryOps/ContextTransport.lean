import Solidity.Backend.MemoryOps.SliceExtension
import Solidity.Semantics.State

/-!
# Existing locals and slice views across context and heap extension

Local identity transport does not imply object-content preservation. The latter
is explicitly supplied by `Heap.Keeps`, discharged for published allocators.
This adds no call-frame implementation or independent source semantics.
-/
namespace Solidity.Backend.MemoryOps

/-- A local alias is weakened to the same identity in the enlarged heap typing. -/
theorem local_ref_wk {C : Contract} {H H' : HTy} {Γ : Ctx} {R : RefTy}
    (e : H <+: H') (env : TEnv C H Γ) (i : Idx Γ (.mem R)) (r : HRef H R)
    (hr : TEnv.get i env = some r) :
    TEnv.get i (TEnv.wk e Γ env) = some (r.wk e) := by
  rw [TEnv.get_wk, hr]
  rfl

/-- A hidden unset local stays unset; growth cannot manufacture an alias. -/
theorem local_unset_wk {C : Contract} {H H' : HTy} {Γ : Ctx} {R : RefTy}
    (e : H <+: H') (env : TEnv C H Γ) (i : Idx Γ (.mem R))
    (hr : TEnv.get i env = none) :
    TEnv.get i (TEnv.wk e Γ env) = none := by
  rw [TEnv.get_wk, hr]
  rfl

/-- Simultaneous context push and heap growth preserve every older local slice. -/
theorem local_slice_push_wk {C : Contract} {H H' : HTy} {Γ : Ctx}
    {R : RefTy} {E : Ty} {t : LTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (env : TEnv C H Γ)
    (i : Idx Γ (.mem R)) (r : HRef H R) (hr : TEnv.get i env = some r)
    (v : t.TDenote C H') (a : ArrTy R E) (start stop : Nat) :
    TEnv.get (Idx.there (u := t) i) (v, TEnv.wk e Γ env) = some (r.wk e) ∧
    sliceElems hp' (r.wk e) a start stop =
      (sliceElems hp r a start stop).map (MVal.wk e E) :=
  ⟨local_ref_wk e env i r hr, sliceElems_keeps e hk r a start stop⟩

/-- Actual `State.adopt` transports the local and keeps the other state fields.
The object-content conclusion still needs the independent `Keeps` premise. -/
theorem adopt_local_slice {C : Contract} {Γ : Ctx} {α : HTy → Type}
    (σ : State C Γ) (g : Grown σ.H α) (hk : Heap.Keeps g.ext σ.heap g.heap)
    {R : RefTy} {E : Ty} (i : Idx Γ (.mem R)) (r : HRef σ.H R)
    (hr : TEnv.get i σ.env = some r) (a : ArrTy R E) (start stop : Nat) :
    TEnv.get i (σ.adopt g).1.env = some (r.wk g.ext) ∧
    sliceElems (σ.adopt g).1.heap (r.wk g.ext) a start stop =
      (sliceElems σ.heap r a start stop).map (MVal.wk g.ext E) ∧
    (σ.adopt g).1.storage = σ.storage ∧ (σ.adopt g).1.net = σ.net ∧
    (σ.adopt g).1.tx = σ.tx ∧ (σ.adopt g).1.selfBalance = σ.selfBalance :=
  ⟨local_ref_wk g.ext σ.env i r hr, sliceElems_keeps g.ext hk r a start stop,
    rfl, rfl, rfl, rfl⟩

/-- A published storage-tree copy preserves every older typed slice. -/
theorem sliceElems_copyStToM {H : HTy} {R : RefTy} {E T : Ty} (hp : Heap H)
    (v : SVal T) (hm : T.mapFree = true) (r : HRef H R) (a : ArrTy R E)
    (start stop : Nat) :
    sliceElems (v.copyStToM hp hm).heap (r.wk (v.copyStToM hp hm).ext) a start stop =
      (sliceElems hp r a start stop).map (MVal.wk (v.copyStToM hp hm).ext E) :=
  sliceElems_keeps _ (SVal.keeps_copyStToM v hm hp) r a start stop

/-- A copied reference is fresh, while each older local alias stays older. -/
theorem copyStToM_old_ne_fresh {H : HTy} {R Q : RefTy} (hp : Heap H)
    (v : SVal (.ref R)) (hm : (Ty.ref R).mapFree = true) (r : HRef H Q) :
    (r.wk (v.copyStToM hp hm).ext).id ≠
      ((v.copyStToM hp hm).val : HRef _ R).id :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le r.id_lt (SVal.copyStToM_id_ge hp v hm))

/-- Published default construction also preserves every old typed slice. -/
theorem sliceElems_allocDefault {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (A : RefTy) (hm : (Ty.ref A).mapFree = true) (r : HRef H R) (a : ArrTy R E)
    (start stop : Nat) :
    sliceElems (hp.allocDefault A hm).heap (r.wk (hp.allocDefault A hm).ext) a start stop =
      (sliceElems hp r a start stop).map (MVal.wk (hp.allocDefault A hm).ext E) :=
  sliceElems_copyStToM hp (SVal.dflt (.ref A)) hm r a start stop

/-- Default construction cannot alias an older object of any reference type. -/
theorem allocDefault_old_ne_fresh {H : HTy} {Q : RefTy} (hp : Heap H)
    (A : RefTy) (hm : (Ty.ref A).mapFree = true) (r : HRef H Q) :
    (r.wk (hp.allocDefault A hm).ext).id ≠
      ((hp.allocDefault A hm).val : HRef _ A).id :=
  copyStToM_old_ne_fresh hp (SVal.dflt (.ref A)) hm r

/-- info: 'Solidity.Backend.MemoryOps.sliceElems_allocDefault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sliceElems_allocDefault
/-- info: 'Solidity.Backend.MemoryOps.allocDefault_old_ne_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocDefault_old_ne_fresh

/-- info: 'Solidity.Backend.MemoryOps.local_slice_push_wk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms local_slice_push_wk
/-- info: 'Solidity.Backend.MemoryOps.adopt_local_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms adopt_local_slice
/-- info: 'Solidity.Backend.MemoryOps.sliceElems_copyStToM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sliceElems_copyStToM
/-- info: 'Solidity.Backend.MemoryOps.copyStToM_old_ne_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copyStToM_old_ne_fresh

end Solidity.Backend.MemoryOps
