import Solidity.Backend.MemoryOps.SnapshotSchedule

/-! Backwards index provenance is observation data only. It neither copies
values nor evaluates a heap. Actual reads are connected to runCaptures by the
existing single-step snapshot theorem, with no final relation as a premise. -/
namespace Solidity.Backend.MemoryOps

def snapshotOrigin (x : SnapshotArgs) (k : Nat) : Nat :=
  if x.2.2 ≤ k ∧ k < x.2.2+(x.2.1-x.1) then x.1+(k-x.2.2) else k

/-- Follow the LAST operation first, then its actual predecessor sources. -/
def captureOrigin : List SnapshotArgs → Nat → Nat
  | [],k => k
  | x::xs,k => snapshotOrigin x (captureOrigin xs k)

theorem captureOrigin_append (xs ys : List SnapshotArgs) (k : Nat) :
    captureOrigin (xs++ys) k = captureOrigin xs (captureOrigin ys k) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,captureOrigin,ih]

theorem snapshotOrigin_in_bounds (N : Nat) (x : SnapshotArgs)
    (hv : SnapshotArgs.Valid N x) (k : Nat) (hk : k < N) : snapshotOrigin x k < N := by
  unfold snapshotOrigin
  split
  next h => exact (show SliceBounds N x.1 x.2.1 from ⟨hv.1,hv.2.1⟩).index (by omega)
  next _ => exact hk

theorem captureOrigin_in_bounds (N : Nat) (xs : List SnapshotArgs)
    (hv : CapturesValid N xs) (k : Nat) (hk : k < N) : captureOrigin xs k < N := by
  induction xs with
  | nil => exact hk
  | cons x xs ih =>
    exact snapshotOrigin_in_bounds N x (hv x List.mem_cons_self) _
      (ih (fun y hy => hv y (List.mem_cons_of_mem x hy)))

theorem captureOrigin_outside (N : Nat) (xs : List SnapshotArgs)
    (hv : CapturesValid N xs) (k : Nat) (hk : N ≤ k) : captureOrigin xs k = k := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem x hy))
    change snapshotOrigin x (captureOrigin xs k) = k
    rw [ht]
    have hx := hv x List.mem_cons_self
    have hcap := hx.2.2
    unfold snapshotOrigin
    rw [if_neg (by omega)]

/-- One actual successful checked step transports every read, including its
exterior, through the backwards source index. -/
theorem checkedCapture_origin {H : HTy} {R : RefTy} {E : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (x : SnapshotArgs)
    (ho : checkedCaptureOverwrite hp r a r a x.1 x.2.1 x.2.2 = some out) (k : Nat) :
    (MObj.elems a (out.get r))[k]? = (MObj.elems a (hp.get r))[snapshotOrigin x k]? := by
  obtain ⟨hs,hd,rfl⟩ := (checkedCaptureOverwrite_some_iff _ _ _ _ _ _ _ _ _).mp ho
  rw [captureOverwrite_read_cases]
  unfold snapshotOrigin
  by_cases hk : x.2.2 ≤ k ∧ k < x.2.2+(x.2.1-x.1)
  · rw [if_pos hk,if_pos hk]
  · rw [if_neg hk,if_neg hk]

/-- Entire actual schedule provenance: the tail read maps into the real
intermediate heap, then the first actual call maps it into INITIAL contents. -/
theorem runCaptures_read {H : HTy} {R : RefTy} {E : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (ho : runCaptures hp r a xs = some out) (k : Nat) :
    (MObj.elems a (out.get r))[k]? = (MObj.elems a (hp.get r))[captureOrigin xs k]? := by
  induction xs generalizing hp with
  | nil => have he := Option.some.inj ho; subst out; rfl
  | cons x xs ih =>
    obtain ⟨mid,hf,ht⟩ := (runCaptures_cons_some hp out r a x xs).mp ho
    rw [ih mid ht]
    exact checkedCapture_origin hp mid r a x hf (captureOrigin xs k)

/-- Complete destination restoration iff its computed INITIAL provenance reads
agree. Intermediate writes may change contents and child representations. -/
theorem runCaptures_target_restore_iff {H : HTy} {R : RefTy} {E : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (ho : runCaptures hp r a xs = some out) :
    out.get r = hp.get r ↔
      ∀ k, (MObj.elems a (hp.get r))[captureOrigin xs k]? = (MObj.elems a (hp.get r))[k]? := by
  constructor
  · intro he k
    have hr := runCaptures_read hp out r a xs ho k
    rw [he] at hr
    exact hr.symm
  · intro ha
    have hv : MObj.elems a (out.get r) = MObj.elems a (hp.get r) := by
      apply List.ext_getElem?
      intro k
      exact (runCaptures_read hp out r a xs ho k).trans (ha k)
    cases a <;> apply Subtype.ext <;> simpa only [MObj.elems_dyn,MObj.elems_fixed] using hv

theorem runCaptures_heap_restore_iff {H : HTy} {R : RefTy} {E : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (ho : runCaptures hp r a xs = some out) :
    out = hp ↔ ∀ k, (MObj.elems a (hp.get r))[captureOrigin xs k]? = (MObj.elems a (hp.get r))[k]? := by
  constructor
  · intro he
    exact (runCaptures_target_restore_iff hp out r a xs ho).mp (congrArg (fun h : Heap H => h.get r) he)
  · intro ha
    apply memoryOps_heap_ext
    intro Q q
    by_cases hid : r.id = q.id
    · obtain ⟨rfl,hq⟩ := HRef.heq_of_id r q hid
      cases hq
      exact (runCaptures_target_restore_iff hp out r a xs ho).mpr ha
    · exact runCaptures_frame hp out r a xs ho q hid

theorem BoolChildRepr.schedule_restore_iff {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hi : BoolChildRepr c address hp sv r) (xs : List SnapshotArgs) (out : Heap H)
    (ho : runCaptures hp r .dyn xs = some out) :
    BoolChildRepr c address out sv r ↔
      ∀ k, (MObj.elems .dyn (hp.get r))[captureOrigin xs k]? = (MObj.elems .dyn (hp.get r))[k]? := by
  rw [hi.at_heap_iff out]
  exact runCaptures_target_restore_iff hp out r .dyn xs ho

/-- info: 'Solidity.Backend.MemoryOps.captureOrigin_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms captureOrigin_append
/-- info: 'Solidity.Backend.MemoryOps.snapshotOrigin_in_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms snapshotOrigin_in_bounds
/-- info: 'Solidity.Backend.MemoryOps.captureOrigin_in_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureOrigin_in_bounds
/-- info: 'Solidity.Backend.MemoryOps.captureOrigin_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureOrigin_outside
/-- info: 'Solidity.Backend.MemoryOps.checkedCapture_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCapture_origin
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_read
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_target_restore_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_target_restore_iff
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_heap_restore_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_heap_restore_iff
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.schedule_restore_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.schedule_restore_iff
end Solidity.Backend.MemoryOps
