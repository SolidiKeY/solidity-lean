import Solidity.Theory.Typed.Obs

/-!
# The typed storage, read along a path

What the simulation (`Evm/Repr.lean`) reads of the typed storage
(`Semantics/Storage.lean`) and the Theory's typed laws
(`Theory/Typed/Obs.lean`) do not state: a live read below a path is the
live read of what is live at the path (`findLiveM_append`), a live read is
a read (`findM_of_findLiveM`), and a default's member is the member's
default (`get_dfltBelow`).  Stated on the `match` twins (`SVal.findLiveM`,
`SVal.findM`), which a proof splits as a `match`; the recursor forms are
equal to them (`SVal.findLive_eq_findLiveM`).
-/

namespace Solidity
namespace Evm

open Semantics (structDef lookupBy setBy tyRank fieldsRank)

/-- A live read below a path is the live read of what is live at the path. -/
theorem findLiveM_append {T U W : Ty} : (x : SVal T) → (p : Path T U) → (r : Path U W) →
    x.findLiveM (p.append r) = (x.findLiveM p).bind (·.findLiveM r)
  | x, .nil, r => by rw [Path.append_nil]; cases x <;> rfl
  | .struct fs, .field hf p, r => by
    rw [Path.append_field]
    simp only [SVal.findLiveM]
    exact findLiveM_append _ p r
  | .array e sh hn, .at i p, r => by
    rw [Path.append_at]
    simp only [SVal.findLiveM]
    split
    · split
      · rename_i x0 _
        exact findLiveM_append x0 p r
      · rfl
    · rfl
  | .fixed e, .atF i p, r => by
    rw [Path.append_atF]
    simp only [SVal.findLiveM]
    split
    · split
      · rename_i x0 _
        exact findLiveM_append x0 p r
      · rfl
    · rfl
  | .map m d, .key k p, r => by
    rw [Path.append_key]
    simp only [SVal.findLiveM]
    split
    · rename_i x0 _
      exact findLiveM_append x0 p r
    · exact findLiveM_append d p r

/-- A live read is a read: the live slots are the first slots. -/
theorem findM_of_findLiveM {T U : Ty} : (x : SVal T) → (p : Path T U) → {w : SVal U} →
    x.findLiveM p = some w → x.findM p = some w
  | x, .nil, w, h => by cases x <;> exact h
  | .struct fs, .field hf p, w, h => by
    simp only [SVal.findLiveM, SVal.findM] at h ⊢
    exact findM_of_findLiveM _ p h
  | .array e sh hn, .at i p, w, h => by
    simp only [SVal.findLiveM, SVal.findM] at h ⊢
    split at h
    · rename_i hi
      split at h
      · rename_i x0 hx
        rw [if_pos hi, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1, hx]
        exact findM_of_findLiveM x0 p h
      · cases h
    · cases h
  | .fixed e, .atF i p, w, h => by
    simp only [SVal.findLiveM, SVal.findM] at h ⊢
    split at h
    · rename_i hi
      split at h
      · rename_i x0 hx
        rw [if_pos hi]
        exact findM_of_findLiveM x0 p h
      · cases h
    · cases h
  | .map m d, .key k p, w, h => by
    simp only [SVal.findLiveM, SVal.findM] at h ⊢
    split at h
    · rename_i x0 hx
      exact findM_of_findLiveM x0 p h
    · exact findM_of_findLiveM d p h

namespace Sto

variable {C : Contract}

/-- `findLive` at a reference, by the `match` twin. -/
theorem findLive_eq {U : Ty} (st : Solidity.Storage C) (r : SRef C U) :
    st.findLive r = (st.get r.hroot).findLiveM r.path := by
  unfold Solidity.Storage.findLive
  rw [SVal.findLive_eq_findLiveM]

/-- `find` at a reference, by the `match` twin. -/
theorem find_eq {U : Ty} (st : Solidity.Storage C) (r : SRef C U) :
    st.find r = (st.get r.hroot).findM r.path := by
  unfold Solidity.Storage.find
  rw [SVal.find_eq_findM]

/-- A live read further along a reference. -/
theorem findLive_append {U W : Ty} (st : Solidity.Storage C) (r : SRef C U) (q : Path U W) :
    st.findLive (r.append q) = (st.findLive r).bind (·.findLiveM q) := by
  rw [findLive_eq, findLive_eq]
  exact findLiveM_append _ r.path q

/-- A live read is a read. -/
theorem find_of_findLive {U : Ty} {st : Solidity.Storage C} {r : SRef C U} {w : SVal U}
    (h : st.findLive r = some w) : st.find r = some w := by
  rw [findLive_eq] at h
  rw [find_eq]
  exact findM_of_findLiveM _ _ h

/-- A save at a reference, by the `match` twin. -/
theorem save_eq {U : Ty} (st : Solidity.Storage C) (r : SRef C U) (new : SVal U) :
    st.save r new = ((st.get r.hroot).saveM r.path new).map (st.set r.hroot) := by
  unfold Solidity.Storage.save
  rw [SVal.save_eq_saveM]
  cases (st.get r.hroot).saveM r.path new <;> rfl

end Sto

/-! ## Defaults -/

/-- A default struct's member is the member's default, below the same rank. -/
theorem get_dfltBelow {f : Name} (k : Nat) (ih : (T : Ty) → tyRank T < k → SVal T) :
    {fs : List (Name × Ty)} → (hk : fieldsRank fs < k) → {T : Ty} →
    (h : lookupBy f fs = some T) →
    ∃ hT : tyRank T < k, (SFields.dfltBelow k ih fs hk).get h = ih T hT
  | [], _, _, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, hk, T, h => by
    rw [SFields.dfltBelow, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      exact ⟨Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hk, by simp only [e, dite_true]⟩
    · simp only [e, dite_false]
      exact get_dfltBelow k ih _ _

/-- A default storage's state variable is its type's default. -/
theorem get_dflt {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    (h : lookupBy f fs = some T) → (SFields.dflt fs).get h = SVal.dflt T
  | [], _, h => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, h => by
    rw [SFields.dflt, SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
    · simp only [e, dite_false]
      exact get_dflt _

end Evm
end Solidity
