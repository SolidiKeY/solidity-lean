import Solidity.Backend.MemoryOps.InterstageBuilders
import Solidity.Theory.Typed.MemMirror

/-! Frame the published recursive typed storage-copy mirror across writes to
old objects. This adds no traversal evaluator, copy implementation or Source
relation. Every recursive node's fresh bound comes from the existing mirror. -/
namespace Solidity.Backend.MemoryOps

mutual
/-- Equal contents at all identities observed by a mirror transport that
existing intrinsic relation. The operation corollary discharges this frame. -/
theorem mirrors_frame {H : HTy} {hp hp' : Heap H} {n : Nat}
    (he : ∀ {R : RefTy} (r : HRef H R), n ≤ r.id → hp'.get r = hp.get r) :
    {T : Ty} → (v : SVal T) → (w : MVal H T) → v.Mirrors hp n w → v.Mirrors hp' n w
  | _, .prim _, _, h => h
  | _, .struct fs, r, h => by
    simp only [SVal.Mirrors] at h ⊢
    refine ⟨h.1, ?_⟩
    rw [he r h.1]
    exact fields_mirrors_frame he fs _ h.2
  | _, .array a _ _, r, h => by
    simp only [SVal.Mirrors] at h ⊢
    refine ⟨h.1, ?_⟩
    rw [he r h.1]
    exact vec_mirrors_frame he a _ h.2
  | _, .fixed a, r, h => by
    simp only [SVal.Mirrors] at h ⊢
    refine ⟨h.1, ?_⟩
    rw [he r h.1]
    exact vec_mirrors_frame he a _ h.2
  | _, .map _ _, _, h => by simp only [SVal.Mirrors] at h

theorem fields_mirrors_frame {H : HTy} {hp hp' : Heap H} {n : Nat}
    (he : ∀ {R : RefTy} (r : HRef H R), n ≤ r.id → hp'.get r = hp.get r) :
    {fs : List (Name × Ty)} → (x : SFields fs) → (o : MFields H fs) →
    x.Mirrors hp n o → x.Mirrors hp' n o
  | _, .nil, _, _ => by simp only [SFields.Mirrors]
  | _, .cons v rest, o, h => by
    simp only [SFields.Mirrors] at h ⊢
    exact ⟨mirrors_frame he v _ h.1, fields_mirrors_frame he rest _ h.2⟩

theorem vec_mirrors_frame {H : HTy} {hp hp' : Heap H} {n : Nat}
    (he : ∀ {R : RefTy} (r : HRef H R), n ≤ r.id → hp'.get r = hp.get r) :
    {E : Ty} → {k : Nat} → (x : SVec E k) → (l : List (MVal H E)) →
    x.Mirrors hp n l → x.Mirrors hp' n l
  | _, _, .nil, _, h => h
  | _, _, .cons v rest, _, h => by
    simp only [SVec.Mirrors] at h ⊢
    obtain ⟨w, ws, rfl, h1, h2⟩ := h
    exact ⟨_, _, rfl, mirrors_frame he v _ h1, vec_mirrors_frame he rest _ h2⟩
end

/-- The published storage-tree copy's entire typed recursive mirror survives
actual second capture into an old object, at arbitrary intrinsic type/depth.
Freshness at every recursive node is supplied by mirrors_copyStToM itself. -/
theorem captureAfterCopy_mirrors {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (u v f : Nat) (hs : SliceBounds (mid.len src sa) u v)
    (hd : f+(v-u) ≤ mid.len dst da) :
    sv.Mirrors (captureAfterCopy mid sv hm src sa dst da u v f hs hd)
      H.length (sv.copyStToM mid hm).val :=
  mirrors_frame (fun r hr => captureAfterCopy_new_frame mid sv hm src sa dst da u v f hs hd r hr)
    sv _ (SVal.mirrors_copyStToM mid sv hm)

/-- Actual multi-object default construction has the same recursive mirror
through second old-object writes, with the original mapFree premise. -/
theorem captureAfterDefault_mirrors {H : HTy} {R Q A : RefTy} {E : Ty}
    (mid : Heap H) (hm : (Ty.ref A).mapFree = true)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (u v f : Nat) (hs : SliceBounds (mid.len src sa) u v)
    (hd : f+(v-u) ≤ mid.len dst da) :
    (SVal.dflt (.ref A)).Mirrors
      (captureAfterCopy mid (SVal.dflt (.ref A)) hm src sa dst da u v f hs hd)
      H.length (mid.allocDefault A hm).val :=
  captureAfterCopy_mirrors mid (SVal.dflt (.ref A)) hm src sa dst da u v f hs hd

/-- info: 'Solidity.Backend.MemoryOps.mirrors_frame' depends on axioms: [propext] -/
#guard_msgs in #print axioms mirrors_frame
/-- info: 'Solidity.Backend.MemoryOps.fields_mirrors_frame' depends on axioms: [propext] -/
#guard_msgs in #print axioms fields_mirrors_frame
/-- info: 'Solidity.Backend.MemoryOps.vec_mirrors_frame' depends on axioms: [propext] -/
#guard_msgs in #print axioms vec_mirrors_frame
/-- info: 'Solidity.Backend.MemoryOps.captureAfterCopy_mirrors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureAfterCopy_mirrors
/-- info: 'Solidity.Backend.MemoryOps.captureAfterDefault_mirrors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureAfterDefault_mirrors
end Solidity.Backend.MemoryOps
