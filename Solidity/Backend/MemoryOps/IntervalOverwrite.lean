import Solidity.Backend.MemoryOps.DisjointOverwrite

/-! Captured writes to separated intervals of the same typed object commute.
This is a local interval case, never an admission restriction. Snapshot sources
are a separate question because a preceding write can change a later source. -/
namespace Solidity.Backend.MemoryOps

/-- Empty intervals are disjoint wherever located; touching ends are allowed. -/
def IntervalsApart (d n e m : Nat) : Prop :=
  n = 0 ∨ m = 0 ∨ d + n ≤ e ∨ e + m ≤ d

theorem replaceSlice_read_cases {α : Type} (xs p : List α) (d i : Nat)
    (h : d + p.length ≤ xs.length) :
    (replaceSlice xs d p)[i]? =
      if d ≤ i ∧ i < d + p.length then p[i - d]? else xs[i]? := by
  by_cases hi : d ≤ i ∧ i < d + p.length
  · rw [if_pos hi]
    have hr := replaceSlice_inside xs p d (i - d) h (by omega)
    simpa only [Nat.add_sub_of_le hi.1] using hr
  · rw [if_neg hi]
    by_cases hb : i < d
    · exact replaceSlice_before xs p d i h hb
    · exact replaceSlice_after xs p d i h (by omega)

/-- Both payloads are already captured. Second capacities follow from unchanged
length, and interval separation is the only commutation case distinction. -/
theorem replaceSlice_comm {α : Type} (xs p q : List α) (d e : Nat)
    (hp : d + p.length ≤ xs.length) (hq : e + q.length ≤ xs.length)
    (hs : IntervalsApart d p.length e q.length) :
    replaceSlice (replaceSlice xs d p) e q = replaceSlice (replaceSlice xs e q) d p := by
  rcases hs with hz | hz | hs | hs
  · have he : p = [] := List.length_eq_zero_iff.mp hz
    rw [he, replaceSlice_empty, replaceSlice_empty]
  · have he : q = [] := List.length_eq_zero_iff.mp hz
    rw [he, replaceSlice_empty, replaceSlice_empty]
  all_goals
    apply List.ext_getElem?
    intro i
    rw [replaceSlice_read_cases (replaceSlice xs d p) q e i (by rw [replaceSlice_length xs p d hp]; exact hq),
      replaceSlice_read_cases (replaceSlice xs e q) p d i (by rw [replaceSlice_length xs q e hq]; exact hp),
      replaceSlice_read_cases xs p d i hp, replaceSlice_read_cases xs q e i hq]
    by_cases hi : d ≤ i ∧ i < d + p.length
    · have hj : ¬ (e ≤ i ∧ i < e + q.length) := by omega
      simp only [if_pos hi, if_neg hj]
    · by_cases hj : e ≤ i ∧ i < e + q.length
      · simp only [if_neg hi, if_pos hj]
      · simp only [if_neg hi, if_neg hj]

/-- Runtime size is unchanged at the written object. -/
theorem overwriteSlice_len {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (d : Nat) (p : List (MVal H E))
    (h : d + p.length ≤ hp.len r a) :
    (overwriteSlice hp r a d p h).len r a = hp.len r a := by
  unfold Heap.len
  rw [overwriteSlice_elems, replaceSlice_length _ _ _ h]

/-- Every typed array length survives, including a same-ID source view. -/
theorem overwriteSlice_all_len {H : HTy} {R Q : RefTy} {E F : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (d : Nat) (p : List (MVal H E))
    (h : d + p.length ≤ hp.len r a) (q : HRef H Q) (b : ArrTy Q F) :
    (overwriteSlice hp r a d p h).len q b = hp.len q b := by
  by_cases he : r.id = q.id
  · obtain ⟨rfl, hh⟩ := HRef.heq_of_id r q he
    cases hh
    cases a <;> cases b <;> exact overwriteSlice_len _ _ _ _ _ _
  · exact overwriteSlice_other_length hp r a d p h q b he

/-- Two actual writes to the same object, deriving the second capacity. -/
def overwriteIntervals {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (d : Nat) (p : List (MVal H E))
    (h : d + p.length ≤ hp.len r a) (e : Nat) (q : List (MVal H E))
    (k : e + q.length ≤ hp.len r a) : Heap H :=
  overwriteSlice (overwriteSlice hp r a d p h) r a e q
    (by rw [overwriteSlice_len]; exact k)

private theorem objs_ext {H : HTy} (Rs : List RefTy) (left right : Objs H Rs)
    (h : ∀ {R : RefTy} (i : Nat) (hi : Rs[i]? = some R),
      Objs.get Rs left i hi = Objs.get Rs right i hi) : left = right := by
  induction Rs with
  | nil => cases left; cases right; rfl
  | cons R Rs ih =>
    apply Prod.ext
    · exact h 0 rfl
    · apply ih
      intro Q i hi
      exact h (i + 1) (by simpa only [List.getElem?_cons_succ] using hi)

/-- Extensionality of the existing dependent heap, with no alternate state. -/
theorem memoryOps_heap_ext {H : HTy} (hp hq : Heap H)
    (h : ∀ {R : RefTy} (r : HRef H R), hp.get r = hq.get r) : hp = hq :=
  objs_ext H hp hq (fun i hi => h ⟨i, hi⟩)

private theorem array_ext {H : HTy} {R : RefTy} {E : Ty} (a : ArrTy R E)
    (x y : MObj H R) (h : MObj.elems a x = MObj.elems a y) : x = y := by
  cases a <;> apply Subtype.ext <;> simpa only [MObj.elems_dyn, MObj.elems_fixed] using h

/-- Other objects are unchanged by both writes. -/
theorem overwriteIntervals_frame {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (d : Nat) (p : List (MVal H E))
    (h : d + p.length ≤ hp.len r a) (e : Nat) (q : List (MVal H E))
    (k : e + q.length ≤ hp.len r a) (s : HRef H Q) (hne : r.id ≠ s.id) :
    (overwriteIntervals hp r a d p h e q k).get s = hp.get s := by
  unfold overwriteIntervals
  rw [overwriteSlice_frame _ r s a e q _ hne, overwriteSlice_frame hp r s a d p h hne]

/-- Actual heap equality for disjoint same-object intervals, preserving all
primitive/reference element types and all other objects. -/
theorem overwriteIntervals_comm {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (d : Nat) (p : List (MVal H E))
    (h : d + p.length ≤ hp.len r a) (e : Nat) (q : List (MVal H E))
    (k : e + q.length ≤ hp.len r a) (hs : IntervalsApart d p.length e q.length) :
    overwriteIntervals hp r a d p h e q k = overwriteIntervals hp r a e q k d p h := by
  apply memoryOps_heap_ext
  intro Q s
  by_cases he : r.id = s.id
  · obtain ⟨rfl, hh⟩ := HRef.heq_of_id r s he
    cases hh
    apply array_ext a
    simp only [overwriteIntervals, overwriteSlice_elems]
    exact replaceSlice_comm _ p q d e h k hs
  · rw [overwriteIntervals_frame hp r a d p h e q k s he,
      overwriteIntervals_frame hp r a e q k d p h s he]

/-- Whole-heap equality transports every published typed path observation. -/
theorem overwriteIntervals_path {C : Contract} {Γ : Ctx} {R : RefTy} {E T : Ty}
    (σ : State C Γ) (r : HRef σ.H R) (a : ArrTy R E)
    (d : Nat) (p : List (MVal σ.H E)) (h : d + p.length ≤ σ.heap.len r a)
    (e : Nat) (q : List (MVal σ.H E)) (k : e + q.length ≤ σ.heap.len r a)
    (hs : IntervalsApart d p.length e q.length) (path : MPath C Γ T) :
    path.mvalT {σ with heap := overwriteIntervals σ.heap r a d p h e q k} =
      path.mvalT {σ with heap := overwriteIntervals σ.heap r a e q k d p h} := by
  rw [overwriteIntervals_comm _ _ _ _ _ _ _ _ _ hs]

/-- info: 'Solidity.Backend.MemoryOps.replaceSlice_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms replaceSlice_comm
/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_all_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_all_len
/-- info: 'Solidity.Backend.MemoryOps.overwriteIntervals_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteIntervals_comm
/-- info: 'Solidity.Backend.MemoryOps.overwriteIntervals_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteIntervals_path
end Solidity.Backend.MemoryOps
