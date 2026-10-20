import Solidity.Typing.CleanTail
import Solidity.Typing.HeredRun

/-!
# Clean tails, kept by a contract that exposes nothing

`Storage.CleanTail` (`Typing/CleanTail.lean`) is not kept by every run: a
write through an alias left past a live end by a shrink (a `pop`, a
`delete`, a copy over a longer array) lands in the slots past the end, and
an empty `push` later exposes it (`docs/options.md`, O6).  It is kept by a
program that never shrinks an array while a storage alias may point into
it (`Prog.exposesNone`): then every alias stays at live slots, every write
lands at live slots, and what lies past an end is only what a clear left,
an ordinary default.

**The invariant** (`CTInv`) is the clean storage and every alias local live
(`Storage.LiveAll`: every dynamic array along its path entered below its
length).  A statement keeps it (`Stmt.keeps_ct`), and where an alias may be
held around it (its own context's, or a caller's: the flag `g`) it also
keeps every live reference live (`Storage.Grows`): such a statement shrinks
no array but one of words, which no alias enters.

**The check** (`Stmt.ctSafe`) is syntactic, on the elaborated program: a
statement that may shrink an array of references (an assignment or a
`delete` of a reference, a copy out of memory, a `pop` of references) only
where no alias is in scope, here or in a caller (`outer`); a recursive call
is not unfolded and fails it.  A contract all of whose functions pass it
keeps clean tails from its deployment on (`ReachableBy.cleanTail`).
-/

namespace Solidity

open Semantics (structDef lookupBy setBy lookupBy_setBy_self lookupBy_setBy_ne
  lookupBy_eq_some_mem)

variable {C : Contract}

/-! ## Live slots, every array -/

/-- Along `p` from `x`, every dynamic array entered below its live length. -/
def SVal.LiveAll : {T U : Ty} → SVal T → Path T U → Prop
  | _, _, _, .nil => True
  | _, _, .struct fs, .field h p => (fs.get h).LiveAll p
  | _, _, @SVal.array _ n e sh _, .at i p =>
    i.1.toNat < n ∧ ∀ y, (e.toList ++ sh.toList)[i.1.toNat]? = some y → y.LiveAll p
  | _, _, .fixed e, .atF i p => ∀ y, e.toList[i.1.toNat]? = some y → y.LiveAll p
  | _, _, .map m d, .key k p =>
    match lookupBy k m.toList with
    | some y => y.LiveAll p
    | none => d.LiveAll p

theorem SVal.liveAll_nil {T : Ty} (x : SVal T) : x.LiveAll .nil := by
  cases x <;> simp only [SVal.LiveAll]

theorem SVal.LiveAll.live : {T U : Ty} → {x : SVal T} → {p : Path T U} → x.LiveAll p →
    x.Live p
  | _, _, x, .nil, _ => SVal.live_nil x
  | _, _, .struct fs, .field h p, hl => by
    simp only [SVal.LiveAll] at hl; simp only [SVal.Live]; exact hl.live
  | _, _, .array e sh _, .at i p, hl => by
    simp only [SVal.LiveAll] at hl; simp only [SVal.Live]
    exact fun y hy => ⟨fun _ => hl.1, (hl.2 y hy).live⟩
  | _, _, .fixed e, .atF i p, hl => by
    simp only [SVal.LiveAll] at hl; simp only [SVal.Live]; exact fun y hy => (hl y hy).live
  | _, _, .map m d, .key k p, hl => by
    simp only [SVal.LiveAll] at hl; simp only [SVal.Live]
    split
    · rename_i y hy; simp only [hy] at hl; exact hl.live
    · rename_i hy; simp only [hy] at hl; exact hl.live

/-- Live along a path, then along what it finds. -/
theorem SVal.liveAll_append : {T R U : Ty} → (x : SVal T) → (p : Path T R) → (q : Path R U) →
    x.LiveAll p → (∀ y, x.findM p = some y → y.LiveAll q) → x.LiveAll (p.append q)
  | _, _, _, x, .nil, q, _, h => by rw [Path.append_nil]; exact h x (SVal.findM_nil' x)
  | _, _, _, .struct fs, .field hf p, q, hp, h => by
    rw [Path.append_field]
    simp only [SVal.LiveAll] at hp ⊢
    exact SVal.liveAll_append _ p q hp fun y hy => h y (by simp only [SVal.findM]; exact hy)
  | _, _, _, .array e sh _, .at i p, q, hp, h => by
    rw [Path.append_at]
    simp only [SVal.LiveAll] at hp ⊢
    refine ⟨hp.1, fun y hy => SVal.liveAll_append y p q (hp.2 y hy) fun z hz => h z ?_⟩
    simp only [SVal.findM, hy]; exact hz
  | _, _, _, .fixed e, .atF i p, q, hp, h => by
    rw [Path.append_atF]
    simp only [SVal.LiveAll] at hp ⊢
    exact fun y hy => SVal.liveAll_append y p q (hp y hy) fun z hz =>
      h z (by simp only [SVal.findM, hy]; exact hz)
  | _, _, _, .map m d, .key k p, q, hp, h => by
    rw [Path.append_key]
    simp only [SVal.LiveAll] at hp ⊢
    split
    · rename_i y hy
      simp only [hy] at hp
      exact SVal.liveAll_append y p q hp fun z hz => h z (by simp only [SVal.findM, hy]; exact hz)
    · rename_i hy
      simp only [hy] at hp
      exact SVal.liveAll_append d p q hp fun z hz => h z (by simp only [SVal.findM, hy]; exact hz)

/-! ## A save at live slots keeps the tails clean -/

/-- **A save keeps clean tails** where it enters every array at a live slot:
what lies past each end is left as it was. -/
theorem SVal.saveM_ct : {T U : Ty} → {x : SVal T} → (p : Path T U) → {new : SVal U} →
    {x' : SVal T} → x.All cleanTailH → new.All cleanTailH → x.LiveAll p →
    x.saveM p new = some x' → x'.All cleanTailH
  | _, _, x, .nil, new, x', _, hn, _, h => by
    cases x <;> (simp only [SVal.saveM, Option.some.injEq] at h; subst h; exact hn)
  | _, _, .struct fs, .field hf p, new, x', hx, hn, hl, h => by
    simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, rfl⟩ := h
    simp only [SVal.All] at hx ⊢
    simp only [SVal.LiveAll] at hl
    exact SFields.all_set hf hx (SVal.saveM_ct p (SFields.all_get hf hx) hn hl hy)
  | _, _, @SVal.array E n e sh _, .at i p, new, x', hx, hn, hl, h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      simp only [SVal.All] at hx ⊢
      simp only [SVal.LiveAll] at hl
      have hall : ∀ w ∈ e.toList ++ sh.toList, w.All cleanTailH := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact SVec.all_iff.mp hx.2.1 w hw
        · exact SList.all_iff.mp hx.2.2 w hw
      have hzA := SVal.saveM_ct p (hall y (List.mem_of_getElem? hy)) hn (hl.2 y hy) hz
      have hset : ∀ w ∈ (e.toList ++ sh.toList).set i.1.toNat z, w.All cleanTailH := by
        intro w hw
        rcases List.mem_or_eq_of_mem_set hw with hw | hw
        · exact hall w hw
        · exact hw ▸ hzA
      have hdrop : ((e.toList ++ sh.toList).set i.1.toNat z).drop n = sh.toList := by
        rw [List.drop_set_of_lt hl.1]
        exact List.drop_left' (SVec.length_toList e)
      refine ⟨?_, SVec.all_ofList.mpr fun w hw => hset w (List.mem_of_mem_take hw),
        SList.all_ofList.mpr fun w hw => hset w (List.mem_of_mem_drop hw)⟩
      change (SList.ofList _).OrdinaryDefault
      rw [hdrop, SList.ordinaryDefault_ofList, ← SList.ordinaryDefault_iff]
      exact hx.1
    · exact nomatch h
  | _, _, .fixed e, .atF i p, new, x', hx, hn, hl, h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      simp only [SVal.All] at hx ⊢
      simp only [SVal.LiveAll] at hl
      have hzA := SVal.saveM_ct p
        (SVec.all_iff.mp hx.2 y (List.mem_of_getElem? hy)) hn (hl y hy) hz
      refine ⟨hx.1, SVec.all_iff.mpr fun w hw => ?_⟩
      rw [SVec.toList_set] at hw
      rcases List.mem_or_eq_of_mem_set hw with hw | hw
      · exact SVec.all_iff.mp hx.2 w hw
      · exact hw ▸ hzA
    · exact nomatch h
  | _, _, .map m d, .key k p, new, x', hx, hn, hl, h => by
    simp only [SVal.All] at hx
    simp only [SVal.LiveAll] at hl
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hzA := SVal.saveM_ct p
        (SMap.all_iff.mp hx.2.1 (k, y) (lookupBy_eq_some_mem hy)) hn
        (by simpa only [hy] using hl) hz
      simp only [SVal.All]
      refine ⟨trivial, SMap.all_ofList.mpr fun e he => ?_, hx.2.2⟩
      rcases mem_setBy he with he | he
      · rw [he]; exact hzA
      · exact SMap.all_iff.mp hx.2.1 e he
    · rename_i hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hzA := SVal.saveM_ct p hx.2.2 hn (by simpa only [hy] using hl) hz
      simp only [SVal.All]
      refine ⟨trivial, SMap.all_ofList.mpr fun e he => ?_, hx.2.2⟩
      rcases mem_setBy he with he | he
      · rw [he]; exact hzA
      · exact SMap.all_iff.mp hx.2.1 e he

/-! ## Growing: every live reference stays live -/

/-- Every reference path live in `x` is live in `y`. -/
def SVal.GrowsTo {T : Ty} (x y : SVal T) : Prop :=
  ∀ (R : RefTy) (p : Path T (.ref R)), x.LiveAll p → y.LiveAll p

theorem SVal.GrowsTo.refl {T : Ty} (x : SVal T) : x.GrowsTo x := fun _ _ h => h

/-- A word has no reference path. -/
theorem SVal.growsTo_prim {q : PrimTy} (x y : SVal (.prim q)) : x.GrowsTo y :=
  fun _ p _ => nomatch Path.eq_prim p

/-- **A save keeps every live reference live** when what it replaces grows
into what it writes: a save keeps every array's length along its path. -/
theorem SVal.saveM_grows : {T U : Ty} → (x : SVal T) → (q : Path T U) → (new : SVal U) →
    {x' : SVal T} → x.saveM q new = some x' →
    (∀ old, x.findM q = some old → old.GrowsTo new) → x.GrowsTo x'
  | _, _, x, .nil, new, x', h, hg => by
    have : x' = new := by
      cases x <;> (simp only [SVal.saveM, Option.some.injEq] at h; exact h.symm)
    subst this
    exact hg x (SVal.findM_nil' x)
  | _, _, .struct fs, .field (f := f0) hf q, new, x', h, hg => by
    simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨z, hz, rfl⟩ := h
    have ih := SVal.saveM_grows _ q new hz fun old ho => hg old (by simp only [SVal.findM]; exact ho)
    intro R p hp
    cases p with
    | nil => exact SVal.liveAll_nil _
    | field hg' p =>
      rename_i g _
      simp only [SVal.LiveAll] at hp ⊢
      by_cases e : g = f0
      · subst e
        cases (Option.some.inj (hf.symm.trans hg'))
        rw [SFields.get_set_same]
        exact ih R p hp
      · rw [SFields.get_set_ne fs hf hg' (Ne.symm e)]
        exact hp
  | _, _, @SVal.array E n e sh hn, .at i q, new, x', h, hg => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have ih := SVal.saveM_grows y q new hz fun old ho =>
        hg old (by simp only [SVal.findM, hy]; exact ho)
      intro R p hp
      cases p with
      | nil => exact SVal.liveAll_nil _
      | «at» j p =>
        simp only [SVal.LiveAll] at hp ⊢
        have hlen : n ≤ (e.toList ++ sh.toList).length := by
          rw [List.length_append, SVec.length_toList]; omega
        refine ⟨?_, fun w hw => ?_⟩
        · simp only [List.length_take, List.length_set]; omega
        · rw [SVec.toList_ofList, SList.toList_ofList, List.take_append_drop,
            List.getElem?_set] at hw
          split at hw
          · rename_i hij
            have hw' : z = w := by
              have := (List.getElem?_eq_some_iff.mp hy).1
              simp only [this, ↓reduceIte, Option.some.injEq] at hw
              exact hw
            subst hw'
            rw [hij] at hy
            exact ih R p (hp.2 y hy)
          · exact hp.2 w hw
    · exact nomatch h
  | _, _, .fixed e, .atF i q, new, x', h, hg => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have ih := SVal.saveM_grows y q new hz fun old ho =>
        hg old (by simp only [SVal.findM, hy]; exact ho)
      intro R p hp
      cases p with
      | nil => exact SVal.liveAll_nil _
      | atF j p =>
        simp only [SVal.LiveAll] at hp ⊢
        intro w hw
        rw [SVec.toList_set, List.getElem?_set] at hw
        split at hw
        · rename_i hij
          have hw' : z = w := by
            have := (List.getElem?_eq_some_iff.mp hy).1
            simp only [this, ↓reduceIte, Option.some.injEq] at hw
            exact hw
          subst hw'
          rw [hij] at hy
          exact ih R p (hp y hy)
        · exact hp w hw
    · exact nomatch h
  | _, _, .map m d, .key k q, new, x', h, hg => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have ih := SVal.saveM_grows y q new hz fun old ho =>
        hg old (by simp only [SVal.findM, hy]; exact ho)
      intro R p hp
      cases p with
      | nil => exact SVal.liveAll_nil _
      | key k' p =>
        simp only [SVal.LiveAll, SMap.toList_ofList] at hp ⊢
        by_cases e : k' = k
        · subst e
          simp only [lookupBy_setBy_self]
          simp only [hy] at hp
          exact ih R p hp
        · simp only [lookupBy_setBy_ne e]
          exact hp
    · rename_i hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have ih := SVal.saveM_grows d q new hz fun old ho =>
        hg old (by simp only [SVal.findM, hy]; exact ho)
      intro R p hp
      cases p with
      | nil => exact SVal.liveAll_nil _
      | key k' p =>
        simp only [SVal.LiveAll, SMap.toList_ofList] at hp ⊢
        by_cases e : k' = k
        · subst e
          simp only [lookupBy_setBy_self]
          simp only [hy] at hp
          exact ih R p hp
        · simp only [lookupBy_setBy_ne e]
          exact hp

/-- An element pushed: every live slot stays live, at what it held. -/
theorem SVal.growsTo_push {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (x : SVal E) (sh' : List (SVal E)) (h' : (e.toList ++ [x]).length < 2 ^ 256) :
    (SVal.array e sh hn).GrowsTo (.array (SVec.ofList (e.toList ++ [x])) (.ofList sh') h') := by
  intro R p hp
  cases p with
  | nil => exact SVal.liveAll_nil _
  | «at» j p =>
    simp only [SVal.LiveAll] at hp ⊢
    have hj : j.1.toNat < e.toList.length := by rw [SVec.length_toList]; exact hp.1
    refine ⟨by rw [List.length_append]; omega, fun w hw => hp.2 w ?_⟩
    rw [SVec.toList_ofList, List.append_assoc, List.getElem?_append_left hj] at hw
    rw [List.getElem?_append_left hj]; exact hw

/-- An array of words: no reference path enters its slots. -/
theorem SVal.growsTo_words {q : PrimTy} {n m : Nat} (e : SVec (.prim q) n) (sh : SList (.prim q))
    (hn : n < 2 ^ 256) (e' : SVec (.prim q) m) (sh' : SList (.prim q)) (hm : m < 2 ^ 256) :
    (SVal.array e sh hn).GrowsTo (.array e' sh' hm) := by
  intro R p hp
  cases p with
  | nil => exact SVal.liveAll_nil _
  | «at» j p => exact nomatch Path.eq_prim p

/-- A reference live in a storage. -/
def Storage.LiveAll (st : Storage C) {U : Ty} (r : SRef C U) : Prop :=
  (st.get r.hroot).LiveAll r.path

/-- Every reference live in `st` is live in `st'`. -/
def Storage.Grows (st st' : Storage C) : Prop :=
  ∀ {R : RefTy} (r : SRef C (.ref R)), st.LiveAll r → st'.LiveAll r

theorem Storage.Grows.refl (st : Storage C) : st.Grows st := fun _ h => h

theorem Storage.Grows.trans {st₁ st₂ st₃ : Storage C} (h₁ : st₁.Grows st₂) (h₂ : st₂.Grows st₃) :
    st₁.Grows st₃ := fun r h => h₂ r (h₁ r h)

/-- **A save keeps every live reference live** when what it replaces grows
into what it writes. -/
theorem Storage.save_grows {st st' : Storage C} {U : Ty} {q : SRef C U} {new : SVal U}
    (h : st.save q new = some st') (hg : ∀ old, st.find q = some old → old.GrowsTo new) :
    st.Grows st' := by
  obtain ⟨v', hv, rfl⟩ := save_eq_some h
  have hgx := SVal.saveM_grows _ _ new hv fun old ho =>
    hg old (by rw [Storage.find, SVal.find_eq_findM]; exact ho)
  intro R r hr
  unfold Storage.LiveAll at hr ⊢
  obtain ⟨rr, rh, rp⟩ := r
  obtain ⟨qr, qh, qp⟩ := q
  dsimp only at hr hgx ⊢
  by_cases e : rr = qr
  · subst e
    cases (Option.some.inj (qh.symm.trans rh))
    rw [SFields.get_set_same]
    exact hgx R rp hr
  · rw [SFields.get_set_ne st qh rh (Ne.symm e)]
    exact hr

end Solidity
