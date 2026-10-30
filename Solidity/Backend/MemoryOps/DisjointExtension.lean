import Solidity.Backend.MemoryOps.DisjointOverwrite
import Solidity.Backend.MemoryOps.SnapshotExtension

/-! Preserving heap growth transports both actual captured writes. The initial
`Keeps` premise is discharged for allocation below. Fresh-object framing concerns
its own contents, not unchanged contents of children it references. -/
namespace Solidity.Backend.MemoryOps

/-- Both capacities and the intermediate preserving relation are derived. -/
theorem overwriteTwo_keeps {H H' : HTy} {R Q : RefTy} {E F : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R E) (offset : Nat) (payload : List (MVal H E))
    (h : offset + payload.length ≤ hp.len r a)
    (q : HRef H Q) (b : ArrTy Q F) (offset' : Nat) (payload' : List (MVal H F))
    (h' : offset' + payload'.length ≤ hp.len q b) (hne : r.id ≠ q.id) :
    Heap.Keeps e (overwriteTwo hp r a offset payload h q b offset' payload' h' hne)
      (overwriteTwo hp' (r.wk e) a offset (payload.map (MVal.wk e E))
        (overwriteSlice_space e hk r a offset payload h)
        (q.wk e) b offset' (payload'.map (MVal.wk e F))
        (overwriteSlice_space e hk q b offset' payload' h') hne) := by
  have hk1 : Heap.Keeps e (overwriteSlice hp r a offset payload h)
      (overwriteSlice hp' (r.wk e) a offset (payload.map (MVal.wk e E))
        (overwriteSlice_space e hk r a offset payload h)) :=
    overwriteSlice_keeps e hk r a offset payload h
  have hq : offset' + payload'.length ≤ (overwriteSlice hp r a offset payload h).len q b := by
    rw [overwriteSlice_other_length hp r a offset payload h q b hne]
    exact h'
  intro T s
  exact overwriteSlice_keeps e hk1 q b offset' payload' hq s

/-- Actual allocation supplies the preserving-growth premise, including
reference-containing newly allocated objects and arbitrary existing payloads. -/
theorem overwriteTwo_alloc {H : HTy} {R Q A : RefTy} {E F : Ty}
    (hp : Heap H) (o : MObj H A)
    (r : HRef H R) (a : ArrTy R E) (offset : Nat) (payload : List (MVal H E))
    (h : offset + payload.length ≤ hp.len r a)
    (q : HRef H Q) (b : ArrTy Q F) (offset' : Nat) (payload' : List (MVal H F))
    (h' : offset' + payload'.length ≤ hp.len q b) (hne : r.id ≠ q.id) :
    let e := List.prefix_append H [A]
    Heap.Keeps e (overwriteTwo hp r a offset payload h q b offset' payload' h' hne)
      (overwriteTwo (hp.alloc o).1 (r.wk e) a offset (payload.map (MVal.wk e E))
        (overwriteSlice_space e (Heap.keeps_alloc hp o) r a offset payload h)
        (q.wk e) b offset' (payload'.map (MVal.wk e F))
        (overwriteSlice_space e (Heap.keeps_alloc hp o) q b offset' payload' h') hne) :=
  overwriteTwo_keeps _ (Heap.keeps_alloc hp o) r a offset payload h q b offset' payload' h' hne

/-- Old destination identities cannot overwrite the newly allocated object's
own fields, even when that object contains aliases to old destination objects. -/
theorem overwriteTwo_alloc_frame {H : HTy} {R Q A : RefTy} {E F : Ty}
    (hp : Heap H) (o : MObj H A)
    (r : HRef H R) (a : ArrTy R E) (offset : Nat) (payload : List (MVal H E))
    (h : offset + payload.length ≤ hp.len r a)
    (q : HRef H Q) (b : ArrTy Q F) (offset' : Nat) (payload' : List (MVal H F))
    (h' : offset' + payload'.length ≤ hp.len q b) (hne : r.id ≠ q.id) :
    let e := List.prefix_append H [A]
    (overwriteTwo (hp.alloc o).1 (r.wk e) a offset (payload.map (MVal.wk e E))
      (overwriteSlice_space e (Heap.keeps_alloc hp o) r a offset payload h)
      (q.wk e) b offset' (payload'.map (MVal.wk e F))
      (overwriteSlice_space e (Heap.keeps_alloc hp o) q b offset' payload' h') hne).get
        (hp.alloc o).2 = (hp.alloc o).1.get (hp.alloc o).2 := by
  exact overwriteTwo_frame _ _ _ _ _ _ _ _ _ _ _ _ _
    (old_ne_fresh hp o r) (old_ne_fresh hp o q)

/-- info: 'Solidity.Backend.MemoryOps.overwriteTwo_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteTwo_keeps
/-- info: 'Solidity.Backend.MemoryOps.overwriteTwo_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteTwo_alloc
/-- info: 'Solidity.Backend.MemoryOps.overwriteTwo_alloc_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteTwo_alloc_frame

end Solidity.Backend.MemoryOps
