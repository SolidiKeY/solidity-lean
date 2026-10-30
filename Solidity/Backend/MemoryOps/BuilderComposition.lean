import Solidity.Backend.MemoryOps.CopyMirrorFrame

/-! Two actual published builders with checked old-object writes between/after
 them. Generation separation is typed logical identity, not byte-address or
 hash injectivity. Copy/default construction remains imported read-only. -/
namespace Solidity.Backend.MemoryOps

/-- All original array lengths survive the first builder and checked snapshot. -/
theorem captureAfterCopy_old_len {H : HTy} {R Q A T : RefTy} {E F : Ty}
    (hp : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (u v f : Nat) (hs : SliceBounds (hp.len src sa) u v) (hd : f+(v-u) ≤ hp.len dst da)
    (q : HRef H T) (a : ArrTy T F) :
    (captureAfterCopy hp sv hm src sa dst da u v f hs hd).len (q.wk (sv.copyStToM hp hm).ext) a = hp.len q a := by
  rw [Heap.Keeps.len (captureAfterCopy_keeps hp sv hm src sa dst da u v f hs hd) q a,
    captureOverwrite_all_len]

/-- A later mirrored reference is beyond every earlier typed identity,
including any earlier root or observed child, regardless of its reference type. -/
theorem generations_mirror_ne {H H' : HTy} {hp : Heap H'} {R Q : RefTy}
    (e : H <+: H') (q : HRef H Q) (v : SVal (.ref R)) (r : HRef H' R)
    (hr : v.Mirrors hp H.length r) : (q.wk e).id ≠ r.id :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le q.id_lt (SVal.Mirrors.id_ge v r hr))

/-- First tree survives actual second allocation by Keeps, then both trees
survive the actual second old-original-destination write. No final mirror or
pairwise within-copy disjointness is assumed. -/
theorem two_builders_mirrors {H : HTy} {R Q A R' Q' B : RefTy} {E F : Ty}
    (hp : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (hs : SliceBounds (hp.len src sa) s t) (hd : d+(t-s) ≤ hp.len dst da)
    (sv' : SVal (.ref B)) (hm' : (Ty.ref B).mapFree = true)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F)
    (u v f : Nat) :
    let g := sv.copyStToM hp hm
    let mid := captureAfterCopy hp sv hm src sa dst da s t d hs hd
    let g' := sv'.copyStToM mid hm'
    ∀ (out : Heap g'.H'),
      checkedCaptureOverwrite g'.heap ((src'.wk g.ext).wk g'.ext) sa'
        ((dst'.wk g.ext).wk g'.ext) da' u v f = some out →
      sv.Mirrors out H.length (MVal.wk g'.ext (.ref A) g.val) ∧
      sv'.Mirrors out g.H'.length g'.val ∧
      ∀ {T : RefTy} (q : HRef g.H' T),
        (q.wk g'.ext).id ≠ (g'.val : HRef _ B).id ∧
        (H.length ≤ q.id → out.get (q.wk g'.ext) = MObj.wk g'.ext T (mid.get q)) := by
  dsimp only
  intro out ho
  let g := sv.copyStToM hp hm
  let mid := captureAfterCopy hp sv hm src sa dst da s t d hs hd
  let g' := sv'.copyStToM mid hm'
  have kg : Heap.Keeps g'.ext mid g'.heap := SVal.keeps_copyStToM sv' hm' mid
  have frame : ∀ {T : RefTy} (r : HRef g'.H' T), H.length ≤ r.id → out.get r = g'.heap.get r := by
    intro T r hr
    apply checkedCaptureOverwrite_frame _ _ _ _ _ _ _ _ _ ho r
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le dst'.id_lt hr)
  have first : sv.Mirrors mid H.length g.val := captureAfterCopy_mirrors hp sv hm src sa dst da s t d hs hd
  have grown : sv.Mirrors g'.heap H.length (MVal.wk g'.ext (.ref A) g.val) :=
    SVal.Mirrors.wk kg sv g.val first
  refine ⟨mirrors_frame frame sv _ grown, ?_, ?_⟩
  · apply mirrors_frame (fun r hr => frame r (Nat.le_trans g.ext.length_le hr)) sv' g'.val
    exact SVal.mirrors_copyStToM mid sv' hm'
  · intro T q
    refine ⟨copyStToM_old_ne_fresh mid sv' hm' q, ?_⟩
    intro hq
    rw [frame (q.wk g'.ext) hq, kg q]

/-- Bounds for the second checked write are derived from original lengths,
not an assumed intermediate representation or frozen first payload. -/
theorem two_builders_success {H : HTy} {R Q A R' Q' B : RefTy} {E F : Ty}
    (hp : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (hs : SliceBounds (hp.len src sa) s t) (hd : d+(t-s) ≤ hp.len dst da)
    (sv' : SVal (.ref B)) (hm' : (Ty.ref B).mapFree = true)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F)
    (u v f : Nat) (hu : SliceBounds (hp.len src' sa') u v) (he : f+(v-u) ≤ hp.len dst' da') :
    let g := sv.copyStToM hp hm
    let mid := captureAfterCopy hp sv hm src sa dst da s t d hs hd
    let g' := sv'.copyStToM mid hm'
    ∃ out, checkedCaptureOverwrite g.heap (src.wk g.ext) sa (dst.wk g.ext) da s t d = some mid ∧
      checkedCaptureOverwrite g'.heap ((src'.wk g.ext).wk g'.ext) sa' ((dst'.wk g.ext).wk g'.ext) da' u v f = some out ∧
      sv.Mirrors out H.length (MVal.wk g'.ext (.ref A) g.val) ∧ sv'.Mirrors out g.H'.length g'.val := by
  dsimp only
  let g := sv.copyStToM hp hm
  let mid := captureAfterCopy hp sv hm src sa dst da s t d hs hd
  have hsu : SliceBounds (mid.len (src'.wk g.ext) sa') u v := by
    rw [captureAfterCopy_old_len]; exact hu
  have hde : f+(v-u) ≤ mid.len (dst'.wk g.ext) da' := by
    rw [captureAfterCopy_old_len]; exact he
  let out := captureAfterCopy mid sv' hm' (src'.wk g.ext) sa' (dst'.wk g.ext) da' u v f hsu hde
  have ho := captureAfterCopy_checked mid sv' hm' (src'.wk g.ext) sa' (dst'.wk g.ext) da' u v f hsu hde
  have hh := two_builders_mirrors hp sv hm src sa dst da s t d hs hd sv' hm' src' sa' dst' da' u v f out ho
  exact ⟨out,captureAfterCopy_checked hp sv hm src sa dst da s t d hs hd,ho,hh.1,hh.2.1⟩

/-- Exact second-stage failures across both actual builders and first write. -/
theorem two_builders_none_iff {H : HTy} {R Q A R' Q' B : RefTy} {E F : Ty}
    (hp : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (s t d : Nat) (hs : SliceBounds (hp.len src sa) s t) (hd : d+(t-s) ≤ hp.len dst da)
    (sv' : SVal (.ref B)) (hm' : (Ty.ref B).mapFree = true)
    (src' : HRef H R') (sa' : ArrTy R' F) (dst' : HRef H Q') (da' : ArrTy Q' F) (u v f : Nat) :
    let g := sv.copyStToM hp hm
    let mid := captureAfterCopy hp sv hm src sa dst da s t d hs hd
    let g' := sv'.copyStToM mid hm'
    checkedCaptureOverwrite g'.heap ((src'.wk g.ext).wk g'.ext) sa' ((dst'.wk g.ext).wk g'.ext) da' u v f = none ↔
      v < u ∨ hp.len src' sa' < v ∨ hp.len dst' da' < f+(v-u) := by
  dsimp only
  let g := sv.copyStToM hp hm
  let mid := captureAfterCopy hp sv hm src sa dst da s t d hs hd
  have hh := copy_interstage_none_iff mid sv' hm' (src'.wk g.ext) sa' (dst'.wk g.ext) da' u v f
  have lsrc : mid.len (src'.wk g.ext) sa' = hp.len src' sa' :=
    captureAfterCopy_old_len hp sv hm src sa dst da s t d hs hd src' sa'
  have ldst : mid.len (dst'.wk g.ext) da' = hp.len dst' da' :=
    captureAfterCopy_old_len hp sv hm src sa dst da s t d hs hd dst' da'
  rw [lsrc, ldst] at hh
  exact hh

/-- info: 'Solidity.Backend.MemoryOps.captureAfterCopy_old_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureAfterCopy_old_len
/-- info: 'Solidity.Backend.MemoryOps.generations_mirror_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms generations_mirror_ne
/-- info: 'Solidity.Backend.MemoryOps.two_builders_mirrors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms two_builders_mirrors
/-- info: 'Solidity.Backend.MemoryOps.two_builders_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms two_builders_success
/-- info: 'Solidity.Backend.MemoryOps.two_builders_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms two_builders_none_iff
end Solidity.Backend.MemoryOps
