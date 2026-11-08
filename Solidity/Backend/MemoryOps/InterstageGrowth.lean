import Solidity.Backend.MemoryOps.SequentialTransport

/-! Growth after an actual first snapshot, before the second capture.
These are compositions of published Heap/Option operations, not a new evaluator,
reference constructor, Source allocation failure or rollback semantics. -/
namespace Solidity.Backend.MemoryOps

/-- General first-write read cases, with potentially different source/destination
objects. An actual successful checked result supplies its bounds. -/
theorem checkedCaptureOverwrite_read_cases {H : HTy} {R Q : RefTy} {E : Ty}
    (hp : Heap H) (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (mid : Heap H)
    (hf : checkedCaptureOverwrite hp src sa dst da s t d = some mid) (k : Nat) :
    (MObj.elems da (mid.get dst))[k]? =
      if d ≤ k ∧ k < d + (t - s) then (MObj.elems sa (hp.get src))[s + (k - d)]?
      else (MObj.elems da (hp.get dst))[k]? := by
  obtain ⟨hs, hd, rfl⟩ := (checkedCaptureOverwrite_some_iff hp src sa dst da s t d mid).mp hf
  have hc : d + (sliceElems hp src sa s t).length ≤ hp.len dst da := by
    rw [sliceElems_length hp src sa hs]; exact hd
  rw [captureOverwrite, overwriteSlice_elems, replaceSlice_read_cases _ _ d k hc,
    sliceElems_length hp src sa hs]
  by_cases hi : d ≤ k ∧ k < d + (t - s)
  · simp only [if_pos hi]
    exact (sliceElems_read hp src sa hs (show k - d < t - s by omega)).1
  · simp only [if_neg hi]

/-- The prefix relation starts at the actual mid, not initial hp. Bounds and
output preservation for the second capture are derived from that relation. -/
theorem checked_interstage_success {H H' : HTy} {R Q R' Q' : RefTy} {E F : Ty}
    (hp : Heap H) (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (mid : Heap H)
    (hf : checkedCaptureOverwrite hp src sa dst da s t d = some mid)
    (e : H <+: H') (mid' : Heap H') (hk : Heap.Keeps e mid mid')
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F)
    (u v f : Nat) (hs : SliceBounds (mid.len src' sa') u v)
    (hd : f + (v - u) ≤ mid.len dst' da') :
    ∃ out', checkedCaptureOverwrite hp src sa dst da s t d = some mid ∧
      checkedCaptureOverwrite mid' (src'.wk e) sa' (dst'.wk e) da' u v f = some out' ∧
      Heap.Keeps e (captureOverwrite mid src' sa' dst' da' u v f hs hd) out' ∧
      ∀ i, i < v - u →
        (MObj.elems da' (out'.get (dst'.wk e)))[f + i]? =
          ((MObj.elems sa' (mid.get src'))[u + i]?).map (MVal.wk e F) := by
  have hs' : SliceBounds (mid'.len (src'.wk e) sa') u v := sliceBounds_keeps e hk src' sa' hs
  have hd' : f + (v - u) ≤ mid'.len (dst'.wk e) da' := by simpa only [hk.len] using hd
  refine ⟨captureOverwrite mid' (src'.wk e) sa' (dst'.wk e) da' u v f hs' hd', hf,
    checkedCaptureOverwrite_some _ _ _ _ _ _ _ _ hs' hd', ?_, ?_⟩
  · intro T q
    exact captureOverwrite_keeps e hk src' sa' dst' da' u v f hs hd q
  · intro i hi
    rw [captureOverwrite_read _ _ _ _ _ _ _ _ i hs' hd' hi, hk src', MObj.elems_wk, List.getElem?_map]

/-- A failed second operation is classified at the real intermediate heap.
The first operation may already have changed values; no rollback is inferred. -/
theorem checked_interstage_none_iff {H H' : HTy} {R Q : RefTy} {E : Ty}
    {mid : Heap H} (e : H <+: H') (mid' : Heap H') (hk : Heap.Keeps e mid mid')
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat) :
    checkedCaptureOverwrite mid' (src.wk e) sa (dst.wk e) da u v f = none ↔
      v < u ∨ mid.len src sa < v ∨ mid.len dst da < f + (v - u) := by
  simp only [checkedCaptureOverwrite_none_iff, hk.len]

/-- The second source is the first destination. Exact recaptured observations
therefore reflect the actual changed first payload after intervening growth. -/
theorem checked_interstage_read_cases {H H' : HTy} {R Q T : RefTy} {E : Ty}
    (hp : Heap H) (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (mid : Heap H)
    (hf : checkedCaptureOverwrite hp src sa dst da s t d = some mid)
    (e : H <+: H') (mid' : Heap H') (hk : Heap.Keeps e mid mid')
    (target : HRef H T) (ta : ArrTy T E) (u v f : Nat) (out' : Heap H')
    (ho : checkedCaptureOverwrite mid' (dst.wk e) da (target.wk e) ta u v f = some out')
    (i : Nat) (hi : i < v - u) :
    (MObj.elems ta (out'.get (target.wk e)))[f + i]? =
      (if d ≤ u + i ∧ u + i < d + (t - s) then (MObj.elems sa (hp.get src))[s + (u + i - d)]?
       else (MObj.elems da (hp.get dst))[u + i]?).map (MVal.wk e E) := by
  have hr := checkedCaptureOverwrite_read mid' (dst.wk e) da (target.wk e) ta u v f i out' ho hi
  rw [hk dst, MObj.elems_wk, List.getElem?_map,
    checkedCaptureOverwrite_read_cases hp src sa dst da s t d mid hf] at hr
  exact hr

/-- Allocate a supplied existing object on mid, then capture from that actual
extended mid. No constructor/default-builder implementation is duplicated. -/
def captureAfterAlloc {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (o : MObj H A) (src : HRef H R) (sa : ArrTy R E)
    (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat)
    (hs : SliceBounds (mid.len src sa) u v) (hd : f + (v - u) ≤ mid.len dst da) : Heap (H ++ [A]) :=
  let e := List.prefix_append H [A]
  captureOverwrite (mid.alloc o).1 (src.wk e) sa (dst.wk e) da u v f
    (sliceBounds_keeps e (Heap.keeps_alloc mid o) src sa hs)
    (by rw [Heap.Keeps.len (Heap.keeps_alloc mid o) dst da]; exact hd)

theorem captureAfterAlloc_checked {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (o : MObj H A) (src : HRef H R) (sa : ArrTy R E)
    (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat)
    (hs : SliceBounds (mid.len src sa) u v) (hd : f + (v - u) ≤ mid.len dst da) :
    checkedCaptureOverwrite (mid.alloc o).1 (src.wk (List.prefix_append H [A])) sa
      (dst.wk (List.prefix_append H [A])) da u v f = some (captureAfterAlloc mid o src sa dst da u v f hs hd) :=
  checkedCaptureOverwrite_some (mid.alloc o).1 (src.wk (List.prefix_append H [A])) sa
    (dst.wk (List.prefix_append H [A])) da u v f
    (sliceBounds_keeps _ (Heap.keeps_alloc mid o) src sa hs)
    (by rw [Heap.Keeps.len (Heap.keeps_alloc mid o) dst da]; exact hd)

theorem captureAfterAlloc_keeps {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (o : MObj H A) (src : HRef H R) (sa : ArrTy R E)
    (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat)
    (hs : SliceBounds (mid.len src sa) u v) (hd : f + (v - u) ≤ mid.len dst da) :
    Heap.Keeps (List.prefix_append H [A]) (captureOverwrite mid src sa dst da u v f hs hd)
      (captureAfterAlloc mid o src sa dst da u v f hs hd) := by
  intro T q
  exact captureOverwrite_keeps _ (Heap.keeps_alloc mid o) src sa dst da u v f hs hd q

/-- Fresh structural contents are exactly the supplied object's weakening.
References in these fields retain old IDs; their referents may subsequently change. -/
theorem captureAfterAlloc_fresh {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (o : MObj H A) (src : HRef H R) (sa : ArrTy R E)
    (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat)
    (hs : SliceBounds (mid.len src sa) u v) (hd : f + (v - u) ≤ mid.len dst da) :
    (captureAfterAlloc mid o src sa dst da u v f hs hd).get (mid.alloc o).2 =
      MObj.wk (List.prefix_append H [A]) A o := by
  rw [checkedCaptureOverwrite_frame _ _ _ _ _ _ _ _ _
    (captureAfterAlloc_checked mid o src sa dst da u v f hs hd) (mid.alloc o).2 (old_ne_fresh mid o dst), Heap.get_alloc]

/-- Actual fresh-array index reads also retain the original fields, weakened. -/
theorem captureAfterAlloc_fresh_index {H : HTy} {R Q A : RefTy} {E F : Ty}
    (mid : Heap H) (o : MObj H A) (src : HRef H R) (sa : ArrTy R E)
    (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat)
    (hs : SliceBounds (mid.len src sa) u v) (hd : f + (v - u) ≤ mid.len dst da)
    (a : ArrTy A F) (i : PrimTy.uint.Denote) :
    (captureAfterAlloc mid o src sa dst da u v f hs hd).index (mid.alloc o).2 a i =
      ((MObj.elems a o)[i.1.toNat]?).map (MVal.wk (List.prefix_append H [A]) F) := by
  simp only [Heap.index, captureAfterAlloc_fresh, MObj.elems_wk, List.getElem?_map]

/-- The allocation corollary observes the first result's actual recaptured values. -/
theorem captureAfterAlloc_read_cases {H : HTy} {R Q T A : RefTy} {E : Ty}
    (hp : Heap H) (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (mid : Heap H)
    (hf : checkedCaptureOverwrite hp src sa dst da s t d = some mid)
    (o : MObj H A) (target : HRef H T) (ta : ArrTy T E) (u v f : Nat)
    (hs : SliceBounds (mid.len dst da) u v) (hd : f + (v - u) ≤ mid.len target ta)
    (i : Nat) (hi : i < v - u) :
    (MObj.elems ta ((captureAfterAlloc mid o dst da target ta u v f hs hd).get
      (target.wk (List.prefix_append H [A]))))[f + i]? =
      (if d ≤ u + i ∧ u + i < d + (t - s) then (MObj.elems sa (hp.get src))[s + (u + i - d)]?
       else (MObj.elems da (hp.get dst))[u + i]?).map (MVal.wk (List.prefix_append H [A]) E) :=
  checked_interstage_read_cases hp src sa dst da s t d mid hf _ _ (Heap.keeps_alloc mid o) target ta u v f _
    (captureAfterAlloc_checked mid o dst da target ta u v f hs hd) i hi

/-- Second-stage failures classify the actual mid lengths after allocation. -/
theorem captureAfterAlloc_none_iff {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (o : MObj H A) (src : HRef H R) (sa : ArrTy R E)
    (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat) :
    checkedCaptureOverwrite (mid.alloc o).1 (src.wk (List.prefix_append H [A])) sa
      (dst.wk (List.prefix_append H [A])) da u v f = none ↔
      v < u ∨ mid.len src sa < v ∨ mid.len dst da < f + (v - u) :=
  checked_interstage_none_iff _ _ (Heap.keeps_alloc mid o) src sa dst da u v f

/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureOverwrite_read_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureOverwrite_read_cases
/-- info: 'Solidity.Backend.MemoryOps.checked_interstage_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked_interstage_success
/-- info: 'Solidity.Backend.MemoryOps.checked_interstage_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked_interstage_none_iff
/-- info: 'Solidity.Backend.MemoryOps.checked_interstage_read_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked_interstage_read_cases
/-- info: 'Solidity.Backend.MemoryOps.captureAfterAlloc_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureAfterAlloc_checked
/-- info: 'Solidity.Backend.MemoryOps.captureAfterAlloc_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureAfterAlloc_keeps
/-- info: 'Solidity.Backend.MemoryOps.captureAfterAlloc_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureAfterAlloc_fresh
/-- info: 'Solidity.Backend.MemoryOps.captureAfterAlloc_fresh_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureAfterAlloc_fresh_index
/-- info: 'Solidity.Backend.MemoryOps.captureAfterAlloc_read_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureAfterAlloc_read_cases
/-- info: 'Solidity.Backend.MemoryOps.captureAfterAlloc_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureAfterAlloc_none_iff
end Solidity.Backend.MemoryOps
