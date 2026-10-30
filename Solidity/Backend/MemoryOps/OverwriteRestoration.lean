import Solidity.Backend.MemoryOps.OverwriteAgreementExact

/-! Exact two-write restoration from INITIAL reads. The last write controls its
whole interval; only surviving cells of the first write must agree. Overlap and
intermediate mutation are supported, with no new semantics or profile bound. -/
namespace Solidity.Backend.MemoryOps

/-- Pure initial-footprint condition, independent of either output heap. -/
def LastWriteAgrees {α : Type} (xs : List α) (d : Nat) (p : List α)
    (e : Nat) (q : List α) : Prop :=
  (∀ i, i < q.length → q[i]? = xs[e+i]?) ∧
  (∀ i, i < p.length → (d+i < e ∨ e+q.length ≤ d+i) → p[i]? = xs[d+i]?)

/-- Necessary and sufficient restoration at arbitrary runtime lengths. Neither
stagewise agreement nor disjoint intervals are required. -/
theorem replaceSlice_twice_eq_iff {α : Type} (xs p q : List α) (d e : Nat)
    (hp : d+p.length ≤ xs.length) (hq : e+q.length ≤ xs.length) :
    replaceSlice (replaceSlice xs d p) e q = xs ↔ LastWriteAgrees xs d p e q := by
  have hq' : e+q.length ≤ (replaceSlice xs d p).length := by
    rw [replaceSlice_length xs p d hp]; exact hq
  constructor
  · intro he
    constructor
    · intro i hi
      have hr := replaceSlice_inside (replaceSlice xs d p) q e i hq' hi
      rw [he] at hr
      exact hr.symm
    · intro i hi hx
      have hr := replaceSlice_read_cases (replaceSlice xs d p) q e (d+i) hq'
      rw [if_neg (by omega),replaceSlice_inside xs p d i hp hi,he] at hr
      exact hr.symm
  · intro ha
    apply List.ext_getElem?
    intro k
    rw [replaceSlice_read_cases (replaceSlice xs d p) q e k hq',replaceSlice_read_cases xs p d k hp]
    by_cases hsecond : e ≤ k ∧ k < e+q.length
    · rw [if_pos hsecond,ha.1 (k-e) (by omega),Nat.add_sub_of_le hsecond.1]
    · rw [if_neg hsecond]
      by_cases hfirst : d ≤ k ∧ k < d+p.length
      · rw [if_pos hfirst,ha.2 (k-d) (by omega) (by omega),Nat.add_sub_of_le hfirst.1]
      · rw [if_neg hfirst]

/-- Intrinsic typed target identity, for primitive and reference elements. -/
theorem overwriteIntervals_target_eq_iff {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (d : Nat)
    (p : List (MVal H E)) (hd : d+p.length ≤ hp.len r a) (e : Nat)
    (q : List (MVal H E)) (he : e+q.length ≤ hp.len r a) :
    (overwriteIntervals hp r a d p hd e q he).get r = hp.get r ↔
      LastWriteAgrees (MObj.elems a (hp.get r)) d p e q := by
  constructor
  · intro h
    have hv := congrArg (MObj.elems a) h
    simp only [overwriteIntervals,overwriteSlice_elems] at hv
    exact (replaceSlice_twice_eq_iff _ p q d e hd he).mp hv
  · intro h
    have hv := (replaceSlice_twice_eq_iff _ p q d e hd he).mpr h
    have hc : MObj.elems a ((overwriteIntervals hp r a d p hd e q he).get r) = MObj.elems a (hp.get r) := by
      simpa only [overwriteIntervals,overwriteSlice_elems] using hv
    cases a <;> apply Subtype.ext <;> simpa only [MObj.elems_dyn,MObj.elems_fixed] using hc

/-- Outside the one typed destination both writes frame every existing object;
therefore this initial condition is also exact whole-heap restoration. -/
theorem overwriteIntervals_eq_self_iff {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (d : Nat)
    (p : List (MVal H E)) (hd : d+p.length ≤ hp.len r a) (e : Nat)
    (q : List (MVal H E)) (he : e+q.length ≤ hp.len r a) :
    overwriteIntervals hp r a d p hd e q he = hp ↔
      LastWriteAgrees (MObj.elems a (hp.get r)) d p e q := by
  constructor
  · intro h
    exact (overwriteIntervals_target_eq_iff hp r a d p hd e q he).mp (congrArg (fun h : Heap H => h.get r) h)
  · intro h
    apply memoryOps_heap_ext
    intro Q k
    by_cases hid : r.id = k.id
    · obtain ⟨rfl,hk⟩ := HRef.heq_of_id r k hid
      cases hk
      exact (overwriteIntervals_target_eq_iff hp r a d p hd e q he).mpr h
    · exact overwriteIntervals_frame hp r a d p hd e q he k hid

/-- Existing arbitrary typed path observations follow actual restored heap
identity, even when the first write changed an observed descendant. -/
theorem overwriteIntervals_path_restore {C : Contract} {Γ : Ctx} {R : RefTy} {E T : Ty}
    (σ : State C Γ) (r : HRef σ.H R) (a : ArrTy R E) (d : Nat)
    (p : List (MVal σ.H E)) (hd : d+p.length ≤ σ.heap.len r a) (e : Nat)
    (q : List (MVal σ.H E)) (he : e+q.length ≤ σ.heap.len r a)
    (ha : LastWriteAgrees (MObj.elems a (σ.heap.get r)) d p e q) (path : MPath C Γ T) :
    path.mvalT {σ with heap := overwriteIntervals σ.heap r a d p hd e q he} = path.mvalT σ := by
  rw [(overwriteIntervals_eq_self_iff σ.heap r a d p hd e q he).mpr ha]

/-- info: 'Solidity.Backend.MemoryOps.replaceSlice_twice_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms replaceSlice_twice_eq_iff
/-- info: 'Solidity.Backend.MemoryOps.overwriteIntervals_target_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteIntervals_target_eq_iff
/-- info: 'Solidity.Backend.MemoryOps.overwriteIntervals_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteIntervals_eq_self_iff
/-- info: 'Solidity.Backend.MemoryOps.overwriteIntervals_path_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteIntervals_path_restore
end Solidity.Backend.MemoryOps
