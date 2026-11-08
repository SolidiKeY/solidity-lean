import Solidity.Backend.MemoryOps.InterstageGrowth
import Solidity.Backend.MemoryOps.CalldataChildExtension

/-! Existing typed child correspondence across an actual first snapshot,
intermediate growth and actual second snapshot. Only old represented objects
are transported; no fresh Source entry or injectivity assumption is created. -/
namespace Solidity.Backend.MemoryOps

theorem BoolChildRepr.checkedCapture {D : Source.Layout} {H : HTy} {R Q : RefTy} {E : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r) (src : HRef H R) (sa : ArrTy R E)
    (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat) (out : Heap H)
    (ho : checkedCaptureOverwrite hp src sa dst da u v f = some out) (hne : dst.id ≠ r.id) :
    BoolChildRepr c address out s r := by
  refine ⟨hr.1, ?_⟩
  rw [checkedCaptureOverwrite_frame hp src sa dst da u v f out ho r hne]
  exact hr.2

theorem RefChildRepr.checkedCapture {D : Source.Layout} {H : HTy} {R Q : RefTy} {E : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r) (src : HRef H R) (sa : ArrTy R E)
    (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat) (out : Heap H)
    (ho : checkedCaptureOverwrite hp src sa dst da u v f = some out)
    (hroot : dst.id ≠ r.id) (hleaf : ∀ b ∈ MObj.elems .dyn (hp.get r), dst.id ≠ b.id) :
    RefChildRepr c address out s r := by
  obtain ⟨hs, hd, rfl⟩ := (checkedCaptureOverwrite_some_iff hp src sa dst da u v f out).mp ho
  exact hr.overwrite dst da f (sliceElems hp src sa u v)
    (by rw [sliceElems_length hp src sa hs]; exact hd) hroot hleaf

/-- Both write frames and the intermediate Keeps fact are initial/operation
facts; output child correspondence is derived for the old weakened identity. -/
theorem BoolChildRepr.interstage {D : Source.Layout} {H H' : HTy} {R Q R' Q' : RefTy} {E F : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat)
    (mid : Heap H) (hf : checkedCaptureOverwrite hp src sa dst da u v f = some mid)
    (e : H <+: H') (mid' : Heap H') (hk : Heap.Keeps e mid mid')
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F) (u' v' f' : Nat)
    (out : Heap H') (ho : checkedCaptureOverwrite mid' (src'.wk e) sa' (dst'.wk e) da' u' v' f' = some out)
    (hfirst : dst.id ≠ r.id) (hsecond : dst'.id ≠ r.id) : BoolChildRepr c address out s (r.wk e) :=
  ((hr.checkedCapture src sa dst da u v f mid hf hfirst).grow e hk).checkedCapture
    (src'.wk e) sa' (dst'.wk e) da' u' v' f' out ho hsecond

/-- Root framing derives the observed descendant set at mid; typed weakening
then derives its grown set for the second frame, not a presumed final relation. -/
theorem RefChildRepr.interstage {D : Source.Layout} {H H' : HTy} {R Q R' Q' : RefTy} {E F : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat)
    (mid : Heap H) (hf : checkedCaptureOverwrite hp src sa dst da u v f = some mid)
    (e : H <+: H') (mid' : Heap H') (hk : Heap.Keeps e mid mid')
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F) (u' v' f' : Nat)
    (out : Heap H') (ho : checkedCaptureOverwrite mid' (src'.wk e) sa' (dst'.wk e) da' u' v' f' = some out)
    (hroot1 : dst.id ≠ r.id) (hroot2 : dst'.id ≠ r.id)
    (hleaf1 : ∀ b ∈ MObj.elems .dyn (hp.get r), dst.id ≠ b.id)
    (hleaf2 : ∀ b ∈ MObj.elems .dyn (hp.get r), dst'.id ≠ b.id) : RefChildRepr c address out s (r.wk e) := by
  apply ((hr.checkedCapture src sa dst da u v f mid hf hroot1 hleaf1).grow e hk).checkedCapture
    (src'.wk e) sa' (dst'.wk e) da' u' v' f' out ho hroot2
  intro b hb
  rw [hk r, MObj.elems_wk] at hb
  change b ∈ (MObj.elems .dyn (mid.get r)).map (HRef.wk e) at hb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
  rw [checkedCaptureOverwrite_frame hp src sa dst da u v f mid hf r hroot1] at hq
  exact hleaf2 q hq

/-- Actual allocation on the first capture result discharges interstage growth.
The supplied object is not built here and receives no Source representation. -/
theorem BoolChildRepr.captureAfterFirstAlloc {D : Source.Layout} {H : HTy} {R Q R' Q' A : RefTy} {E F : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat)
    (hs : SliceBounds (hp.len src sa) u v) (hd : f + (v - u) ≤ hp.len dst da)
    (o : MObj H A) (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F) (u' v' f' : Nat)
    (hs' : SliceBounds ((captureOverwrite hp src sa dst da u v f hs hd).len src' sa') u' v')
    (hd' : f' + (v' - u') ≤ (captureOverwrite hp src sa dst da u v f hs hd).len dst' da')
    (hfirst : dst.id ≠ r.id) (hsecond : dst'.id ≠ r.id) :
    BoolChildRepr c address
      (captureAfterAlloc (captureOverwrite hp src sa dst da u v f hs hd) o src' sa' dst' da' u' v' f' hs' hd')
      s (r.wk (List.prefix_append H [A])) :=
  hr.interstage src sa dst da u v f _ (checkedCaptureOverwrite_some hp src sa dst da u v f hs hd)
    _ _ (Heap.keeps_alloc _ o) src' sa' dst' da' u' v' f' _
    (captureAfterAlloc_checked _ o src' sa' dst' da' u' v' f' hs' hd') hfirst hsecond

/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.checkedCapture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.checkedCapture
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.checkedCapture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.checkedCapture
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.interstage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.interstage
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.interstage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.interstage
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.captureAfterFirstAlloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.captureAfterFirstAlloc
end Solidity.Backend.MemoryOps
