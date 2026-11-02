import Solidity.Backend.MemoryOps.InterstageCorrespondence
import Solidity.Backend.MemoryOps.ContextTransport

/-! Actual published multi-object storage/default growth between captures.
The implementation of construction/copy is imported read-only. Bounds belong
 to the actual first output; these laws do not compile allocation or deep copy. -/
namespace Solidity.Backend.MemoryOps

def captureAfterCopy {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (u v f : Nat) (hs : SliceBounds (mid.len src sa) u v)
    (hd : f + (v - u) ≤ mid.len dst da) : Heap (sv.copyStToM mid hm).H' :=
  let g := sv.copyStToM mid hm
  captureOverwrite g.heap (src.wk g.ext) sa (dst.wk g.ext) da u v f
    (sliceBounds_keeps g.ext (SVal.keeps_copyStToM sv hm mid) src sa hs)
    (by rw [Heap.Keeps.len (SVal.keeps_copyStToM sv hm mid) dst da]; exact hd)

theorem captureAfterCopy_checked {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (u v f : Nat) (hs : SliceBounds (mid.len src sa) u v)
    (hd : f + (v - u) ≤ mid.len dst da) :
    let g := sv.copyStToM mid hm
    checkedCaptureOverwrite g.heap (src.wk g.ext) sa (dst.wk g.ext) da u v f =
      some (captureAfterCopy mid sv hm src sa dst da u v f hs hd) :=
  checkedCaptureOverwrite_some _ _ _ _ _ _ _ _
    (sliceBounds_keeps _ (SVal.keeps_copyStToM sv hm mid) src sa hs)
    (by rw [Heap.Keeps.len (SVal.keeps_copyStToM sv hm mid) dst da]; exact hd)

theorem captureAfterCopy_keeps {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (u v f : Nat) (hs : SliceBounds (mid.len src sa) u v)
    (hd : f + (v - u) ≤ mid.len dst da) :
    Heap.Keeps (sv.copyStToM mid hm).ext (captureOverwrite mid src sa dst da u v f hs hd)
      (captureAfterCopy mid sv hm src sa dst da u v f hs hd) := by
  intro T r
  exact captureOverwrite_keeps _ (SVal.keeps_copyStToM sv hm mid) src sa dst da u v f hs hd r

theorem captureAfterCopy_fresh {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (u v f : Nat) (hs : SliceBounds (mid.len src sa) u v)
    (hd : f + (v - u) ≤ mid.len dst da) :
    let g := sv.copyStToM mid hm
    H.length ≤ (g.val : HRef _ A).id ∧ (dst.wk g.ext).id ≠ (g.val : HRef _ A).id ∧
      (captureAfterCopy mid sv hm src sa dst da u v f hs hd).get g.val = g.heap.get g.val := by
  refine ⟨SVal.copyStToM_id_ge mid sv hm, copyStToM_old_ne_fresh mid sv hm dst, ?_⟩
  exact checkedCaptureOverwrite_frame _ _ _ _ _ _ _ _ _
    (captureAfterCopy_checked mid sv hm src sa dst da u v f hs hd) _
    (copyStToM_old_ne_fresh mid sv hm dst)

/-- Every observed new object is framed by the actual second old-object write.
This is an object-ID footprint law, not recursive copy or Source liveness. -/
theorem captureAfterCopy_new_frame {H : HTy} {R Q A T : RefTy} {E : Ty}
    (mid : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (u v f : Nat) (hs : SliceBounds (mid.len src sa) u v)
    (hd : f + (v-u) ≤ mid.len dst da)
    (q : HRef (sv.copyStToM mid hm).H' T) (hq : H.length ≤ q.id) :
    (captureAfterCopy mid sv hm src sa dst da u v f hs hd).get q =
      (sv.copyStToM mid hm).heap.get q := by
  apply checkedCaptureOverwrite_frame _ _ _ _ _ _ _ _ _
    (captureAfterCopy_checked mid sv hm src sa dst da u v f hs hd) q
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le dst.id_lt hq)

theorem copy_interstage_none_iff {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat) :
    let g := sv.copyStToM mid hm
    checkedCaptureOverwrite g.heap (src.wk g.ext) sa (dst.wk g.ext) da u v f = none ↔
      v < u ∨ mid.len src sa < v ∨ mid.len dst da < f + (v - u) :=
  checked_interstage_none_iff _ _ (SVal.keeps_copyStToM sv hm mid) src sa dst da u v f

/-- Actual first Some, actual multi-object copy and actual second output. -/
theorem copy_interstage_success {H : HTy} {R Q R' Q' A : RefTy} {E F : Ty}
    (hp : Heap H) (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (mid : Heap H) (hf : checkedCaptureOverwrite hp src sa dst da s t d = some mid)
    (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F)
    (u v f : Nat) (hs : SliceBounds (mid.len src' sa') u v) (hd : f + (v-u) ≤ mid.len dst' da') :
    let g := sv.copyStToM mid hm
    ∃ out, checkedCaptureOverwrite hp src sa dst da s t d = some mid ∧
      checkedCaptureOverwrite g.heap (src'.wk g.ext) sa' (dst'.wk g.ext) da' u v f = some out ∧
      Heap.Keeps g.ext (captureOverwrite mid src' sa' dst' da' u v f hs hd) out ∧
      ∀ i, i < v-u → (MObj.elems da' (out.get (dst'.wk g.ext)))[f+i]? =
        ((MObj.elems sa' (mid.get src'))[u+i]?).map (MVal.wk g.ext F) :=
  checked_interstage_success hp src sa dst da s t d mid hf _ _
    (SVal.keeps_copyStToM sv hm mid) src' sa' dst' da' u v f hs hd

theorem copy_interstage_read_cases {H : HTy} {R Q T A : RefTy} {E : Ty}
    (hp : Heap H) (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (mid : Heap H) (hf : checkedCaptureOverwrite hp src sa dst da s t d = some mid)
    (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (target : HRef H T) (ta : ArrTy T E) (u v f : Nat)
    (hs : SliceBounds (mid.len dst da) u v) (hd : f + (v-u) ≤ mid.len target ta)
    (i : Nat) (hi : i < v-u) :
    let g := sv.copyStToM mid hm
    (MObj.elems ta ((captureAfterCopy mid sv hm dst da target ta u v f hs hd).get (target.wk g.ext)))[f+i]? =
      (if d ≤ u+i ∧ u+i < d+(t-s) then (MObj.elems sa (hp.get src))[s+(u+i-d)]?
       else (MObj.elems da (hp.get dst))[u+i]?).map (MVal.wk g.ext E) :=
  checked_interstage_read_cases hp src sa dst da s t d mid hf _ _
    (SVal.keeps_copyStToM sv hm mid) target ta u v f _
    (captureAfterCopy_checked mid sv hm dst da target ta u v f hs hd) i hi

/-- Default construction is precisely the published copy of the typed default,
including all its actual Grown objects, not a replacement constructor. -/
theorem default_interstage_none_iff {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E) (u v f : Nat) :
    let g := mid.allocDefault A hm
    checkedCaptureOverwrite g.heap (src.wk g.ext) sa (dst.wk g.ext) da u v f = none ↔
      v < u ∨ mid.len src sa < v ∨ mid.len dst da < f+(v-u) :=
  copy_interstage_none_iff mid (SVal.dflt (.ref A)) hm src sa dst da u v f

/-- Identity/alias transport does not require content preservation. -/
theorem copy_interstage_alias {H : HTy} {A R : RefTy} (mid : Heap H)
    (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true) (r q : HRef H R) :
    (r.wk (sv.copyStToM mid hm).ext).id = r.id ∧
    ((r.wk (sv.copyStToM mid hm).ext).id = (q.wk (sv.copyStToM mid hm).ext).id ↔ r.id = q.id) := ⟨rfl, Iff.rfl⟩

theorem BoolChildRepr.captureAfterCopy {D : Source.Layout} {H : HTy} {R Q R' Q' A : RefTy} {E F : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (u v f : Nat) (mid : Heap H) (hf : checkedCaptureOverwrite hp src sa dst da u v f = some mid)
    (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F)
    (u' v' f' : Nat) (hs : SliceBounds (mid.len src' sa') u' v') (hd : f'+(v'-u') ≤ mid.len dst' da')
    (hfirst : dst.id ≠ r.id) (hsecond : dst'.id ≠ r.id) :
    BoolChildRepr c address (captureAfterCopy mid sv hm src' sa' dst' da' u' v' f' hs hd)
      s (r.wk (sv.copyStToM mid hm).ext) :=
  hr.interstage src sa dst da u v f mid hf _ _ (SVal.keeps_copyStToM sv hm mid)
    src' sa' dst' da' u' v' f' _ (captureAfterCopy_checked mid sv hm src' sa' dst' da' u' v' f' hs hd) hfirst hsecond

theorem RefChildRepr.captureAfterCopy {D : Source.Layout} {H : HTy} {R Q R' Q' A : RefTy} {E F : Ty}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (u v f : Nat) (mid : Heap H) (hf : checkedCaptureOverwrite hp src sa dst da u v f = some mid)
    (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F)
    (u' v' f' : Nat) (hs : SliceBounds (mid.len src' sa') u' v') (hd : f'+(v'-u') ≤ mid.len dst' da')
    (hroot1 : dst.id ≠ r.id) (hroot2 : dst'.id ≠ r.id)
    (hleaf1 : ∀ b ∈ MObj.elems .dyn (hp.get r), dst.id ≠ b.id)
    (hleaf2 : ∀ b ∈ MObj.elems .dyn (hp.get r), dst'.id ≠ b.id) :
    RefChildRepr c address (captureAfterCopy mid sv hm src' sa' dst' da' u' v' f' hs hd)
      s (r.wk (sv.copyStToM mid hm).ext) :=
  hr.interstage src sa dst da u v f mid hf _ _ (SVal.keeps_copyStToM sv hm mid)
    src' sa' dst' da' u' v' f' _ (captureAfterCopy_checked mid sv hm src' sa' dst' da' u' v' f' hs hd)
    hroot1 hroot2 hleaf1 hleaf2

/-- info: 'Solidity.Backend.MemoryOps.captureAfterCopy_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureAfterCopy_checked
/-- info: 'Solidity.Backend.MemoryOps.captureAfterCopy_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureAfterCopy_keeps
/-- info: 'Solidity.Backend.MemoryOps.captureAfterCopy_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureAfterCopy_fresh
/-- info: 'Solidity.Backend.MemoryOps.captureAfterCopy_new_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureAfterCopy_new_frame
/-- info: 'Solidity.Backend.MemoryOps.copy_interstage_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_interstage_none_iff
/-- info: 'Solidity.Backend.MemoryOps.copy_interstage_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms copy_interstage_success
/-- info: 'Solidity.Backend.MemoryOps.copy_interstage_read_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_interstage_read_cases
/-- info: 'Solidity.Backend.MemoryOps.default_interstage_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms default_interstage_none_iff
/-- info: 'Solidity.Backend.MemoryOps.copy_interstage_alias' depends on axioms: [propext] -/
#guard_msgs in #print axioms copy_interstage_alias
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.captureAfterCopy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.captureAfterCopy
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.captureAfterCopy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.captureAfterCopy
end Solidity.Backend.MemoryOps
