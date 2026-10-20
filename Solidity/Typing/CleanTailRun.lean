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

/-! ## The storage operations keep clean tails -/

theorem cleanTailH_stripOK : cleanTailH.StripOK := fun {E} _ _ _ _ _ =>
  SList.ordinaryDefault_nil (E := E)

theorem cleanTailH_ovOK : cleanTailH.OvOK := by
  intro E m n oel osh nel nsh ho _ hoel _ _
  change (SList.ofList _).OrdinaryDefault
  rw [SList.ordinaryDefault_ofList]
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    exact SVal.defaultOf_ordinaryDefault u (SVec.all_iff.mp hoel u (List.mem_of_mem_drop hu))
  · exact (SList.ordinaryDefault_iff osh).1 ho w (List.mem_of_mem_drop hw)

/-- A copy out of memory has no slot past an end. -/
theorem SVal.plain_ct {T : Ty} {v : SVal T} (h : v.Plain) : v.All cleanTailH :=
  SVal.all_mono' (P := cleanTailH) (Q := plainH)
    (fun _ _ _ hsh => by
      change _ = _ at hsh
      subst hsh
      exact trivial)
    (fun _ _ _ => trivial) (fun _ _ h => h.elim) v h

/-- Every value of a mapping type is an ordinary default: no clearing
reaches a mapping's entries. -/
theorem SVal.ordinaryDefault_of_isMapping {E : Ty} (hE : E.isMapping = true) (v : SVal E) :
    v.OrdinaryDefault := by
  cases v with
  | prim _ => exact nomatch hE
  | struct _ => exact nomatch hE
  | array _ _ _ => exact nomatch hE
  | fixed _ => exact nomatch hE
  | map m d => exact SVal.ordinaryDefault_map m d

theorem pushSlot_ct {E : Ty} {sh : List (SVal E)} (h : ∀ w ∈ sh, w.All cleanTailH)
    (hd : ∀ w ∈ sh, w.OrdinaryDefault) :
    (pushSlot E sh).1.All cleanTailH ∧ (∀ w ∈ (pushSlot E sh).2, w.All cleanTailH) ∧
      ∀ w ∈ (pushSlot E sh).2, w.OrdinaryDefault := by
  cases sh with
  | nil =>
    exact ⟨SVal.dflt_cleanTail E, fun _ h => by simp only [pushSlot, List.not_mem_nil] at h,
      fun _ h => by simp only [pushSlot, List.not_mem_nil] at h⟩
  | cons c rest =>
    refine ⟨?_, fun w hw => h w (List.mem_cons_of_mem _ hw),
      fun w hw => hd w (List.mem_cons_of_mem _ hw)⟩
    show (if E.isPrimitive then SVal.dflt E else c).All cleanTailH
    split
    · exact SVal.dflt_cleanTail E
    · exact h c List.mem_cons_self

namespace Storage

theorem save_ct {st st' : Storage C} {U : Ty} {r : SRef C U} {new : SVal U}
    (hs : st.All cleanTailH) (hn : new.All cleanTailH) (hl : st.LiveAll r)
    (h : st.save r new = some st') : st'.All cleanTailH := by
  obtain ⟨v', hv, rfl⟩ := save_eq_some h
  exact SFields.all_set r.hroot hs (SVal.saveM_ct r.path (root_all r hs) hn hl hv)

theorem write_ct {st st' : Storage C} {U : Ty} {r : SRef C U} {new : SVal U}
    (hs : st.All cleanTailH) (hn : new.All cleanTailH) (hl : st.LiveAll r)
    (h : st.write r new = some st') : st'.All cleanTailH := by
  unfold Storage.write at h
  split at h
  · exact save_ct hs hn hl h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨old, hold, h⟩ := h
    exact save_ct hs (SVal.overlay_all cleanTailH_stripOK cleanTailH_delOK cleanTailH_ovOK
      old new (find_all hs hold) hn) hl h

theorem delete_ct {st st' : Storage C} {U : Ty} {r : SRef C U}
    (hs : st.All cleanTailH) (hl : st.LiveAll r) (h : st.delete r = some st') :
    st'.All cleanTailH := by
  simp only [Storage.delete, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨old, hold, h⟩ := h
  exact save_ct hs (SVal.defaultOf_all cleanTailH_delOK (find_all hs hold)) hl h

theorem push_ct {st st' : Storage C} {E : Ty} {r : SRef C (.ref (.array E))}
    {val : SVal E → Option (SVal E)} (hs : st.All cleanTailH) (hl : st.LiveAll r)
    (hval : ∀ s x, s.All cleanTailH → val s = some x → x.All cleanTailH)
    (h : st.push r val = some st') : st'.All cleanTailH := by
  unfold Storage.push at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  have hvA := find_all hs hv
  cases v with
  | array e sh hn =>
    simp only [SVal.view_array] at h
    obtain ⟨x, hx, h⟩ := h
    split at h
    · simp only [SVal.All] at hvA
      have hsl := pushSlot_ct (SList.all_iff.mp hvA.2.2)
        ((SList.ordinaryDefault_iff sh).1 hvA.1)
      have hxA := hval _ x hsl.1 hx
      refine save_ct hs ?_ hl h
      simp only [SVal.All]
      refine ⟨?_, SVec.all_ofList.mpr fun w hw => ?_, SList.all_ofList.mpr hsl.2.1⟩
      · change (SList.ofList _).OrdinaryDefault
        rw [SList.ordinaryDefault_ofList]
        exact hsl.2.2
      · rcases List.mem_append.mp hw with hw | hw
        · exact SVec.all_iff.mp hvA.2.1 w hw
        · rw [List.mem_singleton.mp hw]; exact hxA
    · exact nomatch h

theorem pushPlace_ct {st st' : Storage C} {E : Ty} {r : SRef C (.ref (.array E))}
    {k : PrimTy.uint.Denote} (hs : st.All cleanTailH) (hl : st.LiveAll r)
    (h : st.pushPlace r = some (st', k)) : st'.All cleanTailH :=
  push_ct hs hl (fun _ _ hx e => Option.some.inj e ▸ hx) (Storage.push_of_pushPlace h)

theorem pop_ct {st st' : Storage C} {E : Ty} {r : SRef C (.ref (.array E))} {keep : Bool}
    (hs : st.All cleanTailH) (hl : st.LiveAll r) (hkeep : keep = true → E.isMapping = true)
    (h : st.pop keep r = some st') : st'.All cleanTailH := by
  unfold Storage.pop at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  have hvA := find_all hs hv
  cases v with
  | array e sh hn =>
    simp only [SVal.view_array] at h
    split at h
    · exact nomatch h
    · rename_i last rest hrev
      simp only [SVal.All] at hvA
      have hlast : last ∈ e.toList := by
        rw [← List.mem_reverse, hrev]; exact List.mem_cons_self
      have hlA := SVec.all_iff.mp hvA.2.1 last hlast
      have hy : (if keep then last else last.defaultOf).All cleanTailH := by
        split
        · exact hlA
        · exact SVal.defaultOf_all cleanTailH_delOK hlA
      have hyD : (if keep then last else last.defaultOf).OrdinaryDefault := by
        split
        · rename_i hk; exact SVal.ordinaryDefault_of_isMapping (hkeep hk) last
        · exact SVal.defaultOf_ordinaryDefault last hlA
      refine save_ct hs ?_ hl h
      simp only [SVal.All]
      refine ⟨?_,
        SVec.all_ofList.mpr fun w hw => SVec.all_iff.mp hvA.2.1 w (List.dropLast_subset _ hw),
        SList.all_ofList.mpr fun w hw => ?_⟩
      · dsimp only [cleanTailH]
        rw [SList.ordinaryDefault_ofList]
        intro w hw
        rcases List.mem_cons.mp hw with hw | hw
        · rw [hw]; exact hyD
        · exact (SList.ordinaryDefault_iff sh).1 hvA.1 w hw
      · rcases List.mem_cons.mp hw with hw | hw
        · rw [hw]; exact hy
        · exact SList.all_iff.mp hvA.2.2 w hw

/-! ### … and keep live references live -/

theorem save_prim_grows {st st' : Storage C} {q : PrimTy} {r : SRef C (.prim q)}
    {new : SVal (.prim q)} (h : st.save r new = some st') : st.Grows st' :=
  save_grows h fun _ _ => SVal.growsTo_prim _ _

theorem write_prim_grows {st st' : Storage C} {q : PrimTy} {r : SRef C (.prim q)}
    {new : SVal (.prim q)} (h : st.write r new = some st') : st.Grows st' := by
  unfold Storage.write at h
  split at h
  · exact save_prim_grows h
  · rename_i hp; exact absurd rfl hp

theorem delete_prim_grows {st st' : Storage C} {q : PrimTy} {r : SRef C (.prim q)}
    (h : st.delete r = some st') : st.Grows st' := by
  simp only [Storage.delete, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, h⟩ := h
  exact save_prim_grows h

theorem push_grows {st st' : Storage C} {E : Ty} {r : SRef C (.ref (.array E))}
    {val : SVal E → Option (SVal E)} (h : st.push r val = some st') : st.Grows st' := by
  unfold Storage.push at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  cases v with
  | array e sh hn =>
    simp only [SVal.view_array] at h
    obtain ⟨x, _, h⟩ := h
    split at h
    · refine save_grows h fun old ho => ?_
      rw [hv] at ho
      cases ho
      exact SVal.growsTo_push e sh hn x _ _
    · exact nomatch h

theorem pushPlace_grows {st st' : Storage C} {E : Ty} {r : SRef C (.ref (.array E))}
    {k : PrimTy.uint.Denote} (h : st.pushPlace r = some (st', k)) : st.Grows st' :=
  push_grows (Storage.push_of_pushPlace h)

theorem pop_words_grows {st st' : Storage C} {q : PrimTy} {r : SRef C (.ref (.array (.prim q)))}
    {keep : Bool} (h : st.pop keep r = some st') : st.Grows st' := by
  unfold Storage.pop at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, h⟩ := h
  cases v with
  | array e sh hn =>
    simp only [SVal.view_array] at h
    split at h
    · exact nomatch h
    · refine save_grows h fun old ho => ?_
      rw [hv] at ho
      cases ho
      exact SVal.growsTo_words _ _ _ _ _ _

/-- The slot a push appends is live. -/
theorem pushPlace_liveAll {st st' : Storage C} {E : Ty} {r : SRef C (.ref (.array E))}
    {k : PrimTy.uint.Denote} (hl : st.LiveAll r) (h : st.pushPlace r = some (st', k)) :
    st'.LiveAll (r.index (.arr .dyn) k) := by
  obtain ⟨n, e, sh, hn, hcap, rfl, hf⟩ := Storage.pushPlace_shape h
  have hl' : st'.LiveAll r := pushPlace_grows h r hl
  change (st'.get r.hroot).LiveAll (r.path.append (Path.index (.arr .dyn) (lenU n hn)))
  refine SVal.liveAll_append _ _ _ hl' fun y hy => ?_
  have hsame : y = SVal.array (SVec.ofList (e.toList ++ [(pushSlot E sh.toList).1]))
      (.ofList (pushSlot E sh.toList).2) (SVec.snoc_lt_bound e _ hcap) := by
    apply Option.some.inj
    exact hy.symm.trans (by rw [← SVal.find_eq_findM]; exact hf)
  subst y
  rw [Path.index_dyn]
  simp only [SVal.LiveAll]
  refine ⟨?_, fun _ _ => trivial⟩
  simp only [lenU, Int.toNat_natCast, List.length_append, List.length_singleton,
    SVec.length_toList]
  omega

end Storage

end Solidity
