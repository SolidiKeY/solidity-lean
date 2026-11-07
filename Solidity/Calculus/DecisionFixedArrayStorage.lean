import Solidity.Calculus.DecisionFixedArrayPath

/-! # Actual storage observations below a fixed-array prefix
Lift the existing optional typed value reconstruction into Storage, preserving
absence, other roots and diverging paths. No collector or coverage change.
-/
namespace Solidity.Decide

/-- Save the reconstructed enclosing value at exactly its original typed root.
An absent prefix remains none, rather than installing a default value. -/
def fixedFloorStorageAtPath {C : Contract} {a : Name} {T E : Ty} {n : Nat}
    (h : C.rootType a = some T) (p : Path T (.ref (.fixed E n)))
    (B : List Int) (st : Storage C) : Option (Storage C) :=
  (fixedFloorAtPath p B (st.get h)).map (st.set h)

theorem fixedFloorStorageAtPath_absent {C : Contract} {a : Name} {T E : Ty} {n : Nat}
    (h : C.rootType a = some T) (p : Path T (.ref (.fixed E n)))
    (B : List Int) (st : Storage C) (ha : (st.get h).findM p = none) :
    fixedFloorStorageAtPath h p B st = none := by
  rw [fixedFloorStorageAtPath, fixedFloorAtPath_absent p B (st.get h) ha]
  rfl

theorem fixedFloorStorageAtPath_exists {C : Contract} {a : Name} {T E : Ty} {n : Nat}
    (h : C.rootType a = some T) (p : Path T (.ref (.fixed E n)))
    (B : List Int) (st : Storage C) {v : SVal (.ref (.fixed E n))}
    (hv : (st.get h).findM p = some v) :
    ∃ st', fixedFloorStorageAtPath h p B st = some st' := by
  obtain ⟨x', hx⟩ := fixedFloorAtPath_exists p B (st.get h) hv
  refine ⟨st.set h x', ?_⟩
  rw [fixedFloorStorageAtPath, hx]
  rfl

/-- Successful reconstruction exposes its real enclosing-value save. -/
theorem fixedFloorStorageAtPath_saved {C : Contract} {a : Name} {T E : Ty} {n : Nat}
    (h : C.rootType a = some T) (p : Path T (.ref (.fixed E n)))
    (B : List Int) (st : Storage C) {st' : Storage C}
    (hs : fixedFloorStorageAtPath h p B st = some st') :
    ∃ x' : SVal T, fixedFloorAtPath p B (st.get h) = some x' ∧ st.set h x' = st' := by
  exact Option.map_eq_some_iff.mp hs

/-- Full optional indexed lookup, including indices outside the fixed length. -/
theorem fixedFloorStorageAtPath_find {C : Contract} {a : Name} {T E U : Ty} {n : Nat}
    (h : C.rootType a = some T) (p : Path T (.ref (.fixed E n)))
    (B : List Int) (st : Storage C) {st' : Storage C}
    (hs : fixedFloorStorageAtPath h p B st = some st') (hn : (n : Int) ∈ B)
    (i : PrimTy.uint.Denote) (q : Path E U) :
    (st'.get h).findM (p.append (.atF i q)) =
      (st.get h).findM (p.append (.atF (fixedFloorIndex B i) q)) := by
  obtain ⟨x', hx, rfl⟩ := fixedFloorStorageAtPath_saved h p B st hs
  rw [SFields.get_set_same]
  exact fixedFloorAtPath_find p B (st.get h) hx hn i q

/-- The actual word observation is transported without assuming definedness. -/
theorem fixedFloorStorageAtPath_word {C : Contract} {a : Name} {T E : Ty}
    {t : PrimTy} {n : Nat} (h : C.rootType a = some T)
    (p : Path T (.ref (.fixed E n))) (B : List Int) (st : Storage C) {st' : Storage C}
    (hs : fixedFloorStorageAtPath h p B st = some st') (hn : (n : Int) ∈ B)
    (i : PrimTy.uint.Denote) (q : Path E (.prim t)) :
    st'.obs.word (.ref ⟨a, h, p.append (.atF i q)⟩) =
      st.obs.word (.ref ⟨a, h, p.append (.atF (fixedFloorIndex B i) q)⟩) := by
  simp only [Storage.obs_word_ref]
  exact congrArg SVal.wordOf (fixedFloorStorageAtPath_find h p B st hs hn i q)

/-- Presence remains the actual optional lookup's presence, including failure. -/
theorem fixedFloorStorageAtPath_has {C : Contract} {a : Name} {T E U : Ty} {n : Nat}
    (h : C.rootType a = some T) (p : Path T (.ref (.fixed E n)))
    (B : List Int) (st : Storage C) {st' : Storage C}
    (hs : fixedFloorStorageAtPath h p B st = some st') (hn : (n : Int) ∈ B)
    (i : PrimTy.uint.Denote) (q : Path E U) :
    st'.obs.has (.ref ⟨a, h, p.append (.atF i q)⟩) =
      st.obs.has (.ref ⟨a, h, p.append (.atF (fixedFloorIndex B i) q)⟩) := by
  simp only [Storage.obs_has_ref]
  exact congrArg Option.isSome (fixedFloorStorageAtPath_find h p B st hs hn i q)

/-- Diverging continuations of the same root are unchanged. -/
theorem fixedFloorStorageAtPath_diverges {C : Contract} {a : Name} {T E U : Ty} {n : Nat}
    (h : C.rootType a = some T) (p : Path T (.ref (.fixed E n)))
    (B : List Int) (st : Storage C) {st' : Storage C}
    (hs : fixedFloorStorageAtPath h p B st = some st') (q : Path T U)
    (hd : Path.Diverges p q) : (st'.get h).findM q = (st.get h).findM q := by
  obtain ⟨x', hx, rfl⟩ := fixedFloorStorageAtPath_saved h p B st hs
  rw [SFields.get_set_same]
  exact fixedFloorAtPath_diverges p B (st.get h) hx q hd

/-- Other typed roots retain their complete values, not merely selected reads. -/
theorem fixedFloorStorageAtPath_other_root {C : Contract} {a b : Name}
    {T E U : Ty} {n : Nat} (h : C.rootType a = some T)
    (p : Path T (.ref (.fixed E n))) (B : List Int) (st : Storage C) {st' : Storage C}
    (hs : fixedFloorStorageAtPath h p B st = some st')
    (hb : C.rootType b = some U) (hne : b ≠ a) : st'.get hb = st.get hb := by
  obtain ⟨x', hx, rfl⟩ := fixedFloorStorageAtPath_saved h p B st hs
  exact SFields.get_set_ne st h hb (Ne.symm hne) x'

end Solidity.Decide
