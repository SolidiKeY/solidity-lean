import Solidity.Backend.MemoryOps.SequentialSnapshot
import Solidity.Backend.MemoryOps.CalldataNestedChildren

/-! Compose ordered writes/snapshots with real old-footprint growth and child
correspondence. No immutable Source entries or fresh-root certificates are
manufactured. Initial representation and growth premises remain explicit. -/
namespace Solidity.Backend.MemoryOps

theorem overwriteIntervals_keeps {H H' : HTy} {R : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R E) (d : Nat) (p : List (MVal H E))
    (h : d + p.length ≤ hp.len r a) (f : Nat) (q : List (MVal H E))
    (k : f + q.length ≤ hp.len r a) :
    Heap.Keeps e (overwriteIntervals hp r a d p h f q k)
      (overwriteIntervals hp' (r.wk e) a d (p.map (MVal.wk e E))
        (overwriteSlice_space e hk r a d p h) f (q.map (MVal.wk e E))
        (overwriteSlice_space e hk r a f q k)) := by
  have hk1 : Heap.Keeps e (overwriteSlice hp r a d p h)
      (overwriteSlice hp' (r.wk e) a d (p.map (MVal.wk e E)) (overwriteSlice_space e hk r a d p h)) :=
    overwriteSlice_keeps e hk r a d p h
  intro T t
  exact overwriteSlice_keeps e hk1 r a f q (by rw [overwriteSlice_len]; exact k) t

/-- Two actual sequential captures transport through initial preserving growth;
the second growth premise is the derived first-output Keeps, not initial hp. -/
theorem captureTwice_keeps {H H' : HTy} {R : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d + (t - s) ≤ hp.len r a)
    (u v f : Nat) (hu : SliceBounds (hp.len r a) u v)
    (he : f + (v - u) ≤ hp.len r a) :
    Heap.Keeps e (captureTwice hp r a s t d hs hd u v f hu he)
      (captureTwice hp' (r.wk e) a s t d (by simpa only [hk.len] using hs)
        (by simpa only [hk.len] using hd) u v f (by simpa only [hk.len] using hu)
        (by simpa only [hk.len] using he)) := by
  have hk1 : Heap.Keeps e (captureOverwrite hp r a r a s t d hs hd)
      (captureOverwrite hp' (r.wk e) a (r.wk e) a s t d
        (by simpa only [hk.len] using hs) (by simpa only [hk.len] using hd)) :=
    captureOverwrite_keeps e hk r a r a s t d hs hd
  intro T q
  exact captureOverwrite_keeps e hk1 r a r a u v f
    (by simpa only [captureOverwrite_all_len] using hu)
    (by simpa only [captureOverwrite_all_len] using he) q

/-- Existing represented child contents survive both actual writes when the
child object is separate. This is not a premise about the final heap. -/
theorem BoolChildRepr.overwriteIntervals {D : Source.Layout} {H : HTy} {R : RefTy} {E : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r) (dst : HRef H R) (a : ArrTy R E)
    (d : Nat) (p : List (MVal H E)) (h : d + p.length ≤ hp.len dst a)
    (f : Nat) (q : List (MVal H E)) (k : f + q.length ≤ hp.len dst a)
    (hne : dst.id ≠ r.id) :
    BoolChildRepr c address (overwriteIntervals hp dst a d p h f q k) s r :=
  (hr.overwrite dst a d p h hne).overwrite dst a f q
    (by rw [overwriteSlice_len]; exact k) hne

/-- The same root/leaf footprint is derived for both writes; first-write root
framing supplies the second observed leaf set. -/
theorem RefChildRepr.overwriteIntervals {D : Source.Layout} {H : HTy} {R : RefTy} {E : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r) (dst : HRef H R) (a : ArrTy R E)
    (d : Nat) (p : List (MVal H E)) (h : d + p.length ≤ hp.len dst a)
    (f : Nat) (q : List (MVal H E)) (k : f + q.length ≤ hp.len dst a)
    (hroot : dst.id ≠ r.id) (hleaf : ∀ b ∈ MObj.elems .dyn (hp.get r), dst.id ≠ b.id) :
    RefChildRepr c address (overwriteIntervals hp dst a d p h f q k) s r := by
  apply (hr.overwrite dst a d p h hroot hleaf).overwrite dst a f q
    (by rw [overwriteSlice_len]; exact k) hroot
  intro b hb
  rw [overwriteSlice_frame hp dst r a d p h hroot] at hb
  exact hleaf b hb

/-- Successful Option composition transports both actual intermediate heaps. -/
theorem checkedCaptureSequence_keeps {H H' : HTy} {R Q R' Q' : RefTy} {E F : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (s t d : Nat)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F) (u v f : Nat)
    (out : Heap H) (ho : checkedCaptureSequence hp src sa dst da s t d src' sa' dst' da' u v f = some out) :
    ∃ out', checkedCaptureSequence hp' (src.wk e) sa (dst.wk e) da s t d
      (src'.wk e) sa' (dst'.wk e) da' u v f = some out' ∧ Heap.Keeps e out out' := by
  obtain ⟨mid, hfirst, hsecond⟩ := (checkedCaptureSequence_some_iff hp src sa dst da s t d src' sa' dst' da' u v f out).mp ho
  obtain ⟨mid', hfirst', hk1⟩ := checkedCaptureOverwrite_keeps e hk src sa dst da s t d mid hfirst
  obtain ⟨out', hsecond', hk2⟩ := checkedCaptureOverwrite_keeps e hk1 src' sa' dst' da' u v f out hsecond
  exact ⟨out', (checkedCaptureSequence_some_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr ⟨mid', hfirst', hsecond'⟩, hk2⟩

/-- Failure observations are also transported, independently of payload values. -/
theorem checkedCaptureSequence_none_keeps {H H' : HTy} {R Q R' Q' : RefTy} {E F : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (s t d : Nat)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F) (u v f : Nat) :
    checkedCaptureSequence hp' (src.wk e) sa (dst.wk e) da s t d
      (src'.wk e) sa' (dst'.wk e) da' u v f = none ↔
      checkedCaptureSequence hp src sa dst da s t d src' sa' dst' da' u v f = none := by
  simp only [checkedCaptureSequence_none_iff, hk.len]

/-- info: 'Solidity.Backend.MemoryOps.overwriteIntervals_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteIntervals_keeps
/-- info: 'Solidity.Backend.MemoryOps.captureTwice_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureTwice_keeps
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.overwriteIntervals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.overwriteIntervals
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.overwriteIntervals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.overwriteIntervals
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureSequence_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureSequence_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureSequence_none_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureSequence_none_keeps
end Solidity.Backend.MemoryOps
