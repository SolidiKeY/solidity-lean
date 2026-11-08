import Solidity.Backend.MemoryOps.HeapSnapshot

/-!
# Disjoint overwrite composition on the actual intrinsic heap

Payloads are captured before either write. Distinct object identities derive
all second-write capacity obligations. No storage-copy loop or target emitter
is introduced. Equality is of existing heaps, hence preserves every existing
typed memory-path observation, including reference results and bounds failures.
-/
namespace Solidity.Backend.MemoryOps

private theorem objects_eq {H : HTy} (Rs : List RefTy) (left right : Objs H Rs)
    (h : ∀ {R : RefTy} (i : Nat) (hi : Rs[i]? = some R),
      Objs.get Rs left i hi = Objs.get Rs right i hi) : left = right := by
  induction Rs with
  | nil => cases left; cases right; rfl
  | cons R Rs ih =>
    apply Prod.ext
    · exact h 0 rfl
    · apply ih
      intro Q i hi
      have ht : (R :: Rs)[i + 1]? = some Q := by
        simpa only [List.getElem?_cons_succ] using hi
      exact h (i + 1) ht

private theorem heap_eq {H : HTy} (left right : Heap H)
    (h : ∀ {R : RefTy} (r : HRef H R), left.get r = right.get r) : left = right :=
  objects_eq H left right (fun i hi => h ⟨i, hi⟩)

private theorem heap_set_comm {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (q : HRef H Q) (x : MObj H R) (y : MObj H Q)
    (hne : r.id ≠ q.id) : (hp.set r x).set q y = (hp.set q y).set r x := by
  apply heap_eq
  intro T s
  by_cases hr : r.id = s.id
  · obtain ⟨rfl, he⟩ := HRef.heq_of_id r s hr
    cases he
    rw [Heap.get_set_ne _ q r hne.symm, Heap.get_set_same, Heap.get_set_same]
  · by_cases hq : q.id = s.id
    · obtain ⟨rfl, he⟩ := HRef.heq_of_id q s hq
      cases he
      rw [Heap.get_set_same, Heap.get_set_ne _ r q hne, Heap.get_set_same]
    · rw [Heap.get_set_ne _ q s hq, Heap.get_set_ne _ r s hr,
        Heap.get_set_ne _ r s hr, Heap.get_set_ne _ q s hq]

private theorem withElems_self {H : HTy} {R : RefTy} {E : Ty}
    (a : ArrTy R E) (o : MObj H R) : withElems a o (MObj.elems a o) rfl = o := by
  cases a <;> apply Subtype.ext <;> simp only [withElems, MObj.elems_dyn, MObj.elems_fixed]

/-- Empty overwrite is the identity on the actual heap, at every valid endpoint. -/
theorem overwriteSlice_empty {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (offset : Nat)
    (h : offset + ([] : List (MVal H E)).length ≤ hp.len r a) :
    overwriteSlice hp r a offset [] h = hp := by
  apply heap_eq
  intro Q q
  by_cases he : r.id = q.id
  · obtain ⟨rfl, hh⟩ := HRef.heq_of_id r q he
    cases hh
    rw [overwriteSlice, Heap.get_set_same]
    simpa only [replaceSlice_empty] using withElems_self a (hp.get r)
  · exact overwriteSlice_frame hp r q a offset [] h he

/-- A different object's runtime length is preserved by an overwrite. -/
theorem overwriteSlice_other_length {H : HTy} {R Q : RefTy} {E F : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (offset : Nat)
    (payload : List (MVal H E)) (h : offset + payload.length ≤ hp.len r a)
    (q : HRef H Q) (b : ArrTy Q F) (hne : r.id ≠ q.id) :
    (overwriteSlice hp r a offset payload h).len q b = hp.len q b := by
  unfold Heap.len
  rw [overwriteSlice_frame hp r q a offset payload h hne]

/-- Two existing-object overwrites; the second capacity is derived from the
original capacity and separation rather than postulated about the result. -/
def overwriteTwo {H : HTy} {R Q : RefTy} {E F : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (offset : Nat) (payload : List (MVal H E))
    (h : offset + payload.length ≤ hp.len r a)
    (q : HRef H Q) (b : ArrTy Q F) (offset' : Nat) (payload' : List (MVal H F))
    (h' : offset' + payload'.length ≤ hp.len q b) (hne : r.id ≠ q.id) : Heap H :=
  overwriteSlice (overwriteSlice hp r a offset payload h) q b offset' payload'
    (by rw [overwriteSlice_other_length hp r a offset payload h q b hne]; exact h')

/-- Disjoint captured overwrites commute as actual heaps, for primitive and
reference elements alike, with no payload-size or traversal-depth cutoff. -/
theorem overwriteTwo_comm {H : HTy} {R Q : RefTy} {E F : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (offset : Nat) (payload : List (MVal H E))
    (h : offset + payload.length ≤ hp.len r a)
    (q : HRef H Q) (b : ArrTy Q F) (offset' : Nat) (payload' : List (MVal H F))
    (h' : offset' + payload'.length ≤ hp.len q b) (hne : r.id ≠ q.id) :
    overwriteTwo hp r a offset payload h q b offset' payload' h' hne =
      overwriteTwo hp q b offset' payload' h' r a offset payload h hne.symm := by
  simp only [overwriteTwo, overwriteSlice, Heap.get_set_ne hp r q hne,
    Heap.get_set_ne hp q r hne.symm]
  exact heap_set_comm hp r q _ _ hne

/-- The second, distinct write retains the first destination object. -/
theorem overwriteTwo_first {H : HTy} {R Q : RefTy} {E F : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (offset : Nat) (payload : List (MVal H E))
    (h : offset + payload.length ≤ hp.len r a)
    (q : HRef H Q) (b : ArrTy Q F) (offset' : Nat) (payload' : List (MVal H F))
    (h' : offset' + payload'.length ≤ hp.len q b) (hne : r.id ≠ q.id) :
    (overwriteTwo hp r a offset payload h q b offset' payload' h' hne).get r =
      (overwriteSlice hp r a offset payload h).get r := by
  unfold overwriteTwo
  exact overwriteSlice_frame _ q r b offset' payload' _ hne.symm

/-- All other objects are unchanged by both writes. -/
theorem overwriteTwo_frame {H : HTy} {R Q T : RefTy} {E F : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (offset : Nat) (payload : List (MVal H E))
    (h : offset + payload.length ≤ hp.len r a)
    (q : HRef H Q) (b : ArrTy Q F) (offset' : Nat) (payload' : List (MVal H F))
    (h' : offset' + payload'.length ≤ hp.len q b) (hne : r.id ≠ q.id)
    (s : HRef H T) (hr : r.id ≠ s.id) (hq : q.id ≠ s.id) :
    (overwriteTwo hp r a offset payload h q b offset' payload' h' hne).get s = hp.get s := by
  unfold overwriteTwo
  rw [overwriteSlice_frame _ q s b offset' payload' _ hq,
    overwriteSlice_frame hp r s a offset payload h hr]

/-- Every published typed memory path observes the same result in either
order, including nested aliases, reference-valued results and reverts. -/
theorem overwriteTwo_path {C : Contract} {Γ : Ctx} {R Q : RefTy} {E F T : Ty}
    (σ : State C Γ) (r : HRef σ.H R) (a : ArrTy R E) (offset : Nat)
    (payload : List (MVal σ.H E)) (h : offset + payload.length ≤ σ.heap.len r a)
    (q : HRef σ.H Q) (b : ArrTy Q F) (offset' : Nat) (payload' : List (MVal σ.H F))
    (h' : offset' + payload'.length ≤ σ.heap.len q b) (hne : r.id ≠ q.id)
    (path : MPath C Γ T) :
    path.mvalT {σ with heap := overwriteTwo σ.heap r a offset payload h q b offset' payload' h' hne} =
      path.mvalT {σ with heap := overwriteTwo σ.heap q b offset' payload' h' r a offset payload h hne.symm} := by
  rw [overwriteTwo_comm]

/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_empty
/-- info: 'Solidity.Backend.MemoryOps.overwriteTwo_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteTwo_comm
/-- info: 'Solidity.Backend.MemoryOps.overwriteTwo_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteTwo_path

end Solidity.Backend.MemoryOps
