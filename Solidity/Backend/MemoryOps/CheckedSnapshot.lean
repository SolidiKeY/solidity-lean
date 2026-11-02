import Solidity.Backend.MemoryOps.DisjointOverwrite
import Solidity.Backend.MemoryOps.SnapshotExtension

/-! Checked bounds around the existing actual-heap captureOverwrite operation.
None is this adapter's result, not an invented Source/target halt semantics.
The guard admits arbitrary runtime lengths and reference-valued elements. -/
namespace Solidity.Backend.MemoryOps

def checkedCaptureOverwrite {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) : Option (Heap H) :=
  if hs : start ≤ stop ∧ stop ≤ hp.len src sa then
    if hd : offset + (stop - start) ≤ hp.len dst da then
      some (captureOverwrite hp src sa dst da start stop offset ⟨hs.1, hs.2⟩ hd)
    else none
  else none

/-- Rejection is exactly a reversed interval or either actual runtime overrun. -/
theorem checkedCaptureOverwrite_none_iff {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) :
    checkedCaptureOverwrite hp src sa dst da start stop offset = none ↔
      stop < start ∨ hp.len src sa < stop ∨ hp.len dst da < offset + (stop - start) := by
  unfold checkedCaptureOverwrite
  by_cases hs : start ≤ stop ∧ stop ≤ hp.len src sa
  · rw [dif_pos hs]
    by_cases hd : offset + (stop - start) ≤ hp.len dst da
    · rw [dif_pos hd]
      simp only [Option.some_ne_none, false_iff]
      omega
    · rw [dif_neg hd]
      simp only [true_iff]
      omega
  · rw [dif_neg hs]
    simp only [true_iff]
    omega

/-- Actual bounds discharge the guards, without a postcondition premise. -/
theorem checkedCaptureOverwrite_some {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) (hs : SliceBounds (hp.len src sa) start stop)
    (hd : offset + (stop - start) ≤ hp.len dst da) :
    checkedCaptureOverwrite hp src sa dst da start stop offset =
      some (captureOverwrite hp src sa dst da start stop offset hs hd) := by
  unfold checkedCaptureOverwrite
  rw [dif_pos ⟨hs.ordered, hs.bounded⟩, dif_pos hd]

/-- Every successful result is exactly the published captured heap operation. -/
theorem checkedCaptureOverwrite_some_iff {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) (out : Heap H) :
    checkedCaptureOverwrite hp src sa dst da start stop offset = some out ↔
      ∃ (hs : SliceBounds (hp.len src sa) start stop)
        (hd : offset + (stop - start) ≤ hp.len dst da),
        out = captureOverwrite hp src sa dst da start stop offset hs hd := by
  constructor
  · intro h
    unfold checkedCaptureOverwrite at h
    split at h
    next hs =>
      split at h
      next hd => exact ⟨⟨hs.1, hs.2⟩, hd, (Option.some.inj h).symm⟩
      next hd => cases h
    next hs => cases h
  · rintro ⟨hs, hd, rfl⟩
    exact checkedCaptureOverwrite_some hp src sa dst da start stop offset hs hd

/-- Successful overlapping reads observe the original heap snapshot. -/
theorem checkedCaptureOverwrite_read {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset i : Nat) (out : Heap H)
    (h : checkedCaptureOverwrite hp src sa dst da start stop offset = some out)
    (hi : i < stop - start) :
    (MObj.elems da (out.get dst))[offset + i]? = (MObj.elems sa (hp.get src))[start + i]? := by
  obtain ⟨hs, hd, rfl⟩ := (checkedCaptureOverwrite_some_iff hp src sa dst da start stop offset out).mp h
  exact captureOverwrite_read hp src sa dst da start stop offset i hs hd hi

/-- Success also preserves every other typed object. -/
theorem checkedCaptureOverwrite_frame {H : HTy} {R Q T : RefTy} {E : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) (out : Heap H)
    (h : checkedCaptureOverwrite hp src sa dst da start stop offset = some out)
    (q : HRef H T) (hne : dst.id ≠ q.id) : out.get q = hp.get q := by
  obtain ⟨hs, hd, rfl⟩ := (checkedCaptureOverwrite_some_iff hp src sa dst da start stop offset out).mp h
  exact overwriteSlice_frame hp dst q da offset _ _ hne

/-- An empty source interval is actual whole-heap identity, including endpoints. -/
theorem checkedCaptureOverwrite_empty {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start offset : Nat) (hs : start ≤ hp.len src sa) (hd : offset ≤ hp.len dst da) :
    checkedCaptureOverwrite hp src sa dst da start start offset = some hp := by
  have h := checkedCaptureOverwrite_some hp src sa dst da start start offset
    ⟨Nat.le_refl _, hs⟩ (by simpa only [Nat.sub_self, Nat.add_zero] using hd)
  simpa only [captureOverwrite, sliceElems, Nat.sub_self, List.take_zero,
    overwriteSlice_empty] using h

/-- Preserving extension retains the exact failure observations on old views. -/
theorem checkedCaptureOverwrite_none_keeps {H H' : HTy} {R Q : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) :
    checkedCaptureOverwrite hp' (src.wk e) sa (dst.wk e) da start stop offset = none ↔
      checkedCaptureOverwrite hp src sa dst da start stop offset = none := by
  simp only [checkedCaptureOverwrite_none_iff, Heap.len, hk src, hk dst,
    MObj.elems_wk, List.length_map]

/-- Capturing both source and target through preserving growth commutes at
all old typed objects, including source/destination aliases and reference slots. -/
theorem captureOverwrite_keeps {H H' : HTy} {R Q : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) (hs : SliceBounds (hp.len src sa) start stop)
    (hd : offset + (stop - start) ≤ hp.len dst da) :
    Heap.Keeps e (captureOverwrite hp src sa dst da start stop offset hs hd)
      (captureOverwrite hp' (src.wk e) sa (dst.wk e) da start stop offset
        (sliceBounds_keeps e hk src sa hs)
        (by simpa only [Heap.len, hk dst, MObj.elems_wk, List.length_map] using hd)) := by
  intro T t
  simp only [captureOverwrite, sliceElems_keeps e hk]
  exact overwriteSlice_keeps e hk dst da offset (sliceElems hp src sa start stop)
    (by rw [sliceElems_length hp src sa hs]; exact hd) t

/-- A successful checked operation remains successful under preserving growth,
with old output contents transported rather than assumed. -/
theorem checkedCaptureOverwrite_keeps {H H' : HTy} {R Q : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) (out : Heap H)
    (h : checkedCaptureOverwrite hp src sa dst da start stop offset = some out) :
    ∃ out', checkedCaptureOverwrite hp' (src.wk e) sa (dst.wk e) da start stop offset = some out' ∧
      Heap.Keeps e out out' := by
  obtain ⟨hs, hd, rfl⟩ := (checkedCaptureOverwrite_some_iff hp src sa dst da start stop offset out).mp h
  have hs' : SliceBounds (hp'.len (src.wk e) sa) start stop := sliceBounds_keeps e hk src sa hs
  have hd' : offset + (stop - start) ≤ hp'.len (dst.wk e) da := by
    simpa only [Heap.len, hk dst, MObj.elems_wk, List.length_map] using hd
  refine ⟨_, checkedCaptureOverwrite_some hp' (src.wk e) sa (dst.wk e) da start stop offset hs' hd', ?_⟩
  intro T t
  exact captureOverwrite_keeps e hk src sa dst da start stop offset hs hd t

/-- info: 'Solidity.Backend.MemoryOps.captureOverwrite_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureOverwrite_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureOverwrite_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureOverwrite_keeps

/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureOverwrite_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureOverwrite_none_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureOverwrite_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureOverwrite_some_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureOverwrite_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureOverwrite_read
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureOverwrite_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureOverwrite_frame
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureOverwrite_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureOverwrite_empty
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureOverwrite_none_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureOverwrite_none_keeps
end Solidity.Backend.MemoryOps
