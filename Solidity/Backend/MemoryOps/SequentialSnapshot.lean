import Solidity.Backend.MemoryOps.IntervalOverwrite
import Solidity.Backend.MemoryOps.CheckedSnapshot

/-! Ordered composition of existing snapshots. The second payload is captured
from the actual first output. These intrinsic operations and Option observations
are not a Source/target evaluator, rollback semantics or emitted copy loop. -/
namespace Solidity.Backend.MemoryOps

theorem captureOverwrite_all_len {H : HTy} {R Q T : RefTy} {E F : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (hs : SliceBounds (hp.len src sa) s t)
    (hd : d + (t - s) ≤ hp.len dst da) (q : HRef H T) (b : ArrTy T F) :
    (captureOverwrite hp src sa dst da s t d hs hd).len q b = hp.len q b :=
  overwriteSlice_all_len hp dst da d _ _ q b

/-- Exact original-snapshot observation inside and outside the destination. -/
theorem captureOverwrite_read_cases {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d k : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d + (t - s) ≤ hp.len r a) :
    (MObj.elems a ((captureOverwrite hp r a r a s t d hs hd).get r))[k]? =
      if d ≤ k ∧ k < d + (t - s) then (MObj.elems a (hp.get r))[s + (k - d)]?
      else (MObj.elems a (hp.get r))[k]? := by
  have hc : d + (sliceElems hp r a s t).length ≤ hp.len r a := by
    rw [sliceElems_length hp r a hs]; exact hd
  rw [captureOverwrite, overwriteSlice_elems, replaceSlice_read_cases _ _ d k hc]
  rw [sliceElems_length hp r a hs]
  by_cases hi : d ≤ k ∧ k < d + (t - s)
  · simp only [if_pos hi]
    exact (sliceElems_read hp r a hs (show k - d < t - s by omega)).1
  · simp only [if_neg hi]

def captureTwice {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d + (t - s) ≤ hp.len r a)
    (u v e : Nat) (hu : SliceBounds (hp.len r a) u v)
    (he : e + (v - u) ≤ hp.len r a) : Heap H :=
  let mid := captureOverwrite hp r a r a s t d hs hd
  captureOverwrite mid r a r a u v e
    (by simpa only [mid, captureOverwrite_all_len] using hu)
    (by simpa only [mid, captureOverwrite_all_len] using he)

/-- Ordered read cases: second source reads the first output, including values
written by the first destination. Outside second destination, the first result
is retained. No destination-separation premise is required. -/
theorem captureTwice_read_cases {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d + (t - s) ≤ hp.len r a)
    (u v e : Nat) (hu : SliceBounds (hp.len r a) u v)
    (he : e + (v - u) ≤ hp.len r a) (k : Nat) :
    (MObj.elems a ((captureTwice hp r a s t d hs hd u v e hu he).get r))[k]? =
      if e ≤ k ∧ k < e + (v - u) then
        if d ≤ u + (k - e) ∧ u + (k - e) < d + (t - s) then
          (MObj.elems a (hp.get r))[s + (u + (k - e) - d)]?
        else (MObj.elems a (hp.get r))[u + (k - e)]?
      else if d ≤ k ∧ k < d + (t - s) then
        (MObj.elems a (hp.get r))[s + (k - d)]? else (MObj.elems a (hp.get r))[k]? := by
  simp only [captureTwice, captureOverwrite_read_cases]

/-- Inside the second destination, the first destination decides which
original source element was actually recaptured. -/
theorem captureTwice_inside {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d + (t - s) ≤ hp.len r a)
    (u v e : Nat) (hu : SliceBounds (hp.len r a) u v)
    (he : e + (v - u) ≤ hp.len r a) (i : Nat) (hi : i < v - u) :
    (MObj.elems a ((captureTwice hp r a s t d hs hd u v e hu he).get r))[e + i]? =
      if d ≤ u + i ∧ u + i < d + (t - s) then
        (MObj.elems a (hp.get r))[s + (u + i - d)]? else (MObj.elems a (hp.get r))[u + i]? := by
  have hn : e ≤ e + i ∧ e + i < e + (v - u) := by omega
  simpa only [if_pos hn, Nat.add_sub_cancel_left] using
    captureTwice_read_cases hp r a s t d hs hd u v e hu he (e + i)

/-- A different source object is untouched by the first destination write. -/
theorem captureOverwrite_source_other {H : HTy} {R Q T : RefTy} {E F : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (hs : SliceBounds (hp.len src sa) s t)
    (hd : d + (t - s) ≤ hp.len dst da) (q : HRef H T) (b : ArrTy T F)
    (u v : Nat) (hne : dst.id ≠ q.id) :
    sliceElems (captureOverwrite hp src sa dst da s t d hs hd) q b u v = sliceElems hp q b u v := by
  simp only [sliceElems, captureOverwrite, overwriteSlice_frame hp dst q da d _ _ hne]

/-- Same-object source noninterference follows from actual destination/source
interval separation, allowing empty and touching intervals. -/
theorem captureOverwrite_source_apart {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d + (t - s) ≤ hp.len r a)
    (u v : Nat) (hu : SliceBounds (hp.len r a) u v)
    (ha : IntervalsApart d (t - s) u (v - u)) :
    sliceElems (captureOverwrite hp r a r a s t d hs hd) r a u v = sliceElems hp r a u v := by
  have hm : SliceBounds ((captureOverwrite hp r a r a s t d hs hd).len r a) u v := by
    simpa only [captureOverwrite_all_len] using hu
  apply List.ext_getElem?
  intro i
  by_cases hi : i < v - u
  · rw [(sliceElems_read _ r a hm hi).1, (sliceElems_read hp r a hu hi).1,
      captureOverwrite_read_cases]
    have hn : ¬ (d ≤ u + i ∧ u + i < d + (t - s)) := by
      have ho := hu.ordered
      rcases ha with ha | ha | ha | ha <;> omega
    rw [if_neg hn]
  · rw [List.getElem?_eq_none_iff.mpr (by rw [sliceElems_length _ r a hm]; omega),
      List.getElem?_eq_none_iff.mpr (by rw [sliceElems_length hp r a hu]; omega)]

private theorem overwriteSlice_payload_congr {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (d : Nat)
    (p q : List (MVal H E)) (h : d + p.length ≤ hp.len r a)
    (k : d + q.length ≤ hp.len r a) (he : p = q) :
    overwriteSlice hp r a d p h = overwriteSlice hp r a d q k := by
  cases he
  rfl

/-- Under the sufficient source-noninterference condition, the second payload
may be frozen from the initial heap. This alone does not establish commutation. -/
theorem captureTwice_frozen {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d + (t - s) ≤ hp.len r a)
    (u v e : Nat) (hu : SliceBounds (hp.len r a) u v)
    (he : e + (v - u) ≤ hp.len r a) (ha : IntervalsApart d (t - s) u (v - u)) :
    captureTwice hp r a s t d hs hd u v e hu he =
      overwriteIntervals hp r a d (sliceElems hp r a s t)
        (by rw [sliceElems_length hp r a hs]; exact hd)
        e (sliceElems hp r a u v) (by rw [sliceElems_length hp r a hu]; exact he) := by
  unfold captureTwice captureOverwrite overwriteIntervals
  apply overwriteSlice_payload_congr
  exact captureOverwrite_source_apart hp r a s t d hs hd u v hu ha

/-- Both cross-source noninterference facts plus destination separation suffice
for sequential commutation. These conditions are not claimed necessary. -/
theorem captureTwice_comm {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d + (t - s) ≤ hp.len r a)
    (u v e : Nat) (hu : SliceBounds (hp.len r a) u v)
    (he : e + (v - u) ≤ hp.len r a)
    (hdu : IntervalsApart d (t - s) u (v - u))
    (hes : IntervalsApart e (v - u) s (t - s))
    (hde : IntervalsApart d (t - s) e (v - u)) :
    captureTwice hp r a s t d hs hd u v e hu he = captureTwice hp r a u v e hu he s t d hs hd := by
  rw [captureTwice_frozen hp r a s t d hs hd u v e hu he hdu,
    captureTwice_frozen hp r a u v e hu he s t d hs hd hes]
  apply overwriteIntervals_comm
  simpa only [sliceElems_length hp r a hs, sliceElems_length hp r a hu] using hde

/-- Both ordered writes preserve every other object, regardless of overlap. -/
theorem captureTwice_frame {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d + (t - s) ≤ hp.len r a)
    (u v e : Nat) (hu : SliceBounds (hp.len r a) u v)
    (he : e + (v - u) ≤ hp.len r a) (q : HRef H Q) (hne : r.id ≠ q.id) :
    (captureTwice hp r a s t d hs hd u v e hu he).get q = hp.get q := by
  unfold captureTwice captureOverwrite
  rw [overwriteSlice_frame _ r q a e _ _ hne, overwriteSlice_frame hp r q a d _ _ hne]

/-- Option composition of the two existing checked operations, retaining their
order; no rollback or Source halt interpretation is assigned. -/
def checkedCaptureSequence {H : HTy} {R Q R' Q' : RefTy} {E F : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (s t d : Nat)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F) (u v e : Nat) :
    Option (Heap H) :=
  (checkedCaptureOverwrite hp src sa dst da s t d).bind fun mid =>
    checkedCaptureOverwrite mid src' sa' dst' da' u v e

/-- Success exposes both actual ordered intermediate/result heaps. -/
theorem checkedCaptureSequence_some_iff {H : HTy} {R Q R' Q' : RefTy} {E F : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (s t d : Nat)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F) (u v e : Nat)
    (out : Heap H) :
    checkedCaptureSequence hp src sa dst da s t d src' sa' dst' da' u v e = some out ↔
      ∃ mid, checkedCaptureOverwrite hp src sa dst da s t d = some mid ∧
        checkedCaptureOverwrite mid src' sa' dst' da' u v e = some out := by
  unfold checkedCaptureSequence
  cases hf : checkedCaptureOverwrite hp src sa dst da s t d with
  | none =>
    constructor
    · intro h; cases h
    · rintro ⟨mid, hm, _⟩; cases hm
  | some mid =>
    constructor
    · intro h; exact ⟨mid, rfl, h⟩
    · rintro ⟨other, hm, ho⟩; cases hm; exact ho

/-- Exact failure classification remains in original runtime lengths because
the first successful operation preserves every typed array length. -/
theorem checkedCaptureSequence_none_iff {H : HTy} {R Q R' Q' : RefTy} {E F : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (s t d : Nat)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F) (u v e : Nat) :
    checkedCaptureSequence hp src sa dst da s t d src' sa' dst' da' u v e = none ↔
      (t < s ∨ hp.len src sa < t ∨ hp.len dst da < d + (t - s)) ∨
      (v < u ∨ hp.len src' sa' < v ∨ hp.len dst' da' < e + (v - u)) := by
  unfold checkedCaptureSequence
  cases hf : checkedCaptureOverwrite hp src sa dst da s t d with
  | none =>
    constructor
    · intro _; exact .inl ((checkedCaptureOverwrite_none_iff hp src sa dst da s t d).mp hf)
    · intro _; rfl
  | some mid =>
    have hn : ¬ (t < s ∨ hp.len src sa < t ∨ hp.len dst da < d + (t - s)) := by
      intro bad
      have he := (checkedCaptureOverwrite_none_iff hp src sa dst da s t d).mpr bad
      rw [hf] at he
      cases he
    obtain ⟨hs, hd, rfl⟩ := (checkedCaptureOverwrite_some_iff hp src sa dst da s t d mid).mp hf
    simp only [Option.bind_some, checkedCaptureOverwrite_none_iff, captureOverwrite_all_len]
    constructor
    · exact Or.inr
    · rintro (bad | bad)
      · exact (hn bad).elim
      · exact bad

/-- Actual checked execution of the two valid same-object snapshots yields
the ordered captureTwice heap; all intermediate bounds are derived. -/
theorem captureTwice_checked {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d + (t - s) ≤ hp.len r a)
    (u v e : Nat) (hu : SliceBounds (hp.len r a) u v)
    (he : e + (v - u) ≤ hp.len r a) :
    checkedCaptureSequence hp r a r a s t d r a r a u v e =
      some (captureTwice hp r a s t d hs hd u v e hu he) := by
  apply (checkedCaptureSequence_some_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
  refine ⟨_, checkedCaptureOverwrite_some hp r a r a s t d hs hd, ?_⟩
  exact checkedCaptureOverwrite_some _ r a r a u v e
    (by simpa only [captureOverwrite_all_len] using hu)
    (by simpa only [captureOverwrite_all_len] using he)

/-- info: 'Solidity.Backend.MemoryOps.captureTwice_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureTwice_frame
/-- info: 'Solidity.Backend.MemoryOps.captureTwice_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureTwice_checked

/-- info: 'Solidity.Backend.MemoryOps.captureTwice_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureTwice_inside
/-- info: 'Solidity.Backend.MemoryOps.captureTwice_read_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureTwice_read_cases
/-- info: 'Solidity.Backend.MemoryOps.captureOverwrite_source_apart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureOverwrite_source_apart
/-- info: 'Solidity.Backend.MemoryOps.captureTwice_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureTwice_frozen
/-- info: 'Solidity.Backend.MemoryOps.captureTwice_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureTwice_comm
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureSequence_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureSequence_some_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureSequence_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureSequence_none_iff
end Solidity.Backend.MemoryOps
