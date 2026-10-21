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

/-! ## The invariant: clean tails, live aliases -/

/-- Whether a context holds a storage alias. -/
def Ctx.hasAlias : Ctx → Bool
  | [] => false
  | .alias _ :: _ => true
  | .val _ :: Γ => Ctx.hasAlias Γ
  | .mem _ :: Γ => Ctx.hasAlias Γ
  | .old :: Γ => Ctx.hasAlias Γ
  | .oldNet :: Γ => Ctx.hasAlias Γ
  | .kint :: Γ => Ctx.hasAlias Γ

theorem Ctx.hasAlias_cons {t : LTy} {Γ : Ctx} (h : Γ.hasAlias = true) :
    Ctx.hasAlias (t :: Γ) = true := by
  cases t <;> first | rfl | exact h

theorem Ext.hasAlias {Γ Δ : Ctx} (x : Ext Γ Δ) (h : Γ.hasAlias = true) : Δ.hasAlias = true := by
  induction x with
  | refl => exact h
  | push _ ih => exact Ctx.hasAlias_cons ih

theorem Ctx.hasAlias_append {Γ : Ctx} (ρ : Ctx) (h : Γ.hasAlias = true) :
    (ρ ++ Γ).hasAlias = true :=
  Ext.hasAlias (Ext.append Γ ρ) h

/-- A storage alias local is live (an unset one is). -/
def aliasLive (st : Storage C) {H : HTy} : (t : LTy) → t.TDenote C H → Prop
  | .alias _, v => ∀ r, v = some r → st.LiveAll r
  | .val _, _ => True
  | .mem _, _ => True
  | .old, _ => True
  | .oldNet, _ => True
  | .kint, _ => True

/-- **The invariant**: the storage's tails clean, every alias local live. -/
def CTInv {Γ : Ctx} (σ : State C Γ) : Prop :=
  σ.storage.All cleanTailH ∧ TEnv.All (aliasLive σ.storage) σ.env

theorem aliasLive_grows {st st' : Storage C} (hg : st.Grows st') {H : HTy} :
    (t : LTy) → (v : t.TDenote C H) → aliasLive st t v → aliasLive st' t v
  | .alias _, _, h => fun r hr => hg r (h r hr)
  | .val _, _, _ => trivial
  | .mem _, _, _ => trivial
  | .old, _, _ => trivial
  | .oldNet, _, _ => trivial
  | .kint, _, _ => trivial

theorem aliasLive_wk {st : Storage C} {H H' : HTy} (x : H <+: H') :
    (t : LTy) → (v : t.TDenote C H) → aliasLive st t v → aliasLive st t (LTy.TDenote.wk x t v)
  | .alias _, _, h => h
  | .val _, _, _ => trivial
  | .mem _, _, _ => trivial
  | .old, _, _ => trivial
  | .oldNet, _, _ => trivial
  | .kint, _, _ => trivial

theorem env_noAlias (st : Storage C) {H : HTy} :
    {Γ : Ctx} → Γ.hasAlias = false → (e : TEnv C H Γ) → TEnv.All (aliasLive st) e
  | [], _, _ => trivial
  | .alias _ :: _, h, _ => nomatch h
  | .val _ :: Γ, h, e => ⟨trivial, env_noAlias st (Γ := Γ) h e.2⟩
  | .mem _ :: Γ, h, e => ⟨trivial, env_noAlias st (Γ := Γ) h e.2⟩
  | .old :: Γ, h, e => ⟨trivial, env_noAlias st (Γ := Γ) h e.2⟩
  | .oldNet :: Γ, h, e => ⟨trivial, env_noAlias st (Γ := Γ) h e.2⟩
  | .kint :: Γ, h, e => ⟨trivial, env_noAlias st (Γ := Γ) h e.2⟩

theorem env_wk_live {st : Storage C} {H H' : HTy} (x : H <+: H') : {Γ : Ctx} →
    {e : TEnv C H Γ} → TEnv.All (aliasLive st) e → TEnv.All (aliasLive st) (TEnv.wk x Γ e)
  | [], _, _ => trivial
  | t :: _, _, he => ⟨aliasLive_wk x t _ he.1, env_wk_live x he.2⟩

namespace CTInv

variable {Γ : Ctx}

theorem env_grows {st st' : Storage C} (hg : st.Grows st') {H : HTy} {Γ : Ctx}
    {e : TEnv C H Γ} (he : TEnv.All (aliasLive st) e) : TEnv.All (aliasLive st') e :=
  TEnv.All.mono (fun t v h => aliasLive_grows hg t v h) he

/-- The storage replaced by one with clean tails, every live reference kept
live where an alias may be held. -/
theorem withStorage {σ : State C Γ} (h : CTInv σ) {st : Storage C} (hs : st.All cleanTailH)
    (hg : Γ.hasAlias = true → σ.storage.Grows st) : CTInv (σ.withStorage st) := by
  refine ⟨hs, ?_⟩
  cases ha : Γ.hasAlias
  · exact env_noAlias st ha _
  · exact env_grows (hg ha) h.2

theorem setLocal {σ : State C Γ} (h : CTInv σ) {t : LTy} (i : Idx Γ t) {v : t.TDenote C σ.H}
    (hv : aliasLive σ.storage t v) : CTInv (σ.setLocal i v) :=
  ⟨h.1, TEnv.All.set i h.2 hv⟩

theorem push {σ : State C Γ} (h : CTInv σ) {t : LTy} {v : t.TDenote C σ.H}
    (hv : aliasLive σ.storage t v) : CTInv (σ.push v) :=
  ⟨h.1, hv, h.2⟩

theorem drop {Δ : Ctx} {σ : State C Δ} (h : CTInv σ) (x : Ext Γ Δ) : CTInv (σ.drop x) :=
  ⟨h.1, TEnv.All.drop x h.2⟩

theorem adopt {σ : State C Γ} {α : HTy → Type} (h : CTInv σ) (g : Grown σ.H α) :
    CTInv (σ.adopt g).1 :=
  ⟨h.1, env_wk_live g.ext h.2⟩

end CTInv

/-! ## Resolved references are live -/

section Resolve

variable {Γ : Ctx} (σ : State C Γ) (he : TEnv.All (aliasLive σ.storage) σ.env)

include he

mutual

/-- **A location resolves to live slots**: its alias is live, and each
index the program takes it checks against the length. -/
theorem Loc.resolveT_liveAll : {T : Ty} → (l : Loc C Γ T) → ∀ {r : SRef C T},
    l.resolveT σ = .ok r → σ.storage.LiveAll r
  | _, .root _ _, r, h => by
    cases h
    exact SVal.liveAll_nil _
  | _, .field b f hf, r, h => by
    obtain ⟨r0, h0, h⟩ := tbind_ok_inv h
    cases h
    show (σ.storage.get r0.hroot).LiveAll (r0.path.append (.field hf .nil))
    refine SVal.liveAll_append _ _ _ (SPath.resolveT_liveAll b h0) fun y _ => ?_
    cases y with
    | struct fs => simp only [SVal.LiveAll]
  | _, .index it b i, r, h => by
    obtain ⟨r0, h0, h⟩ := tbind_ok_inv h
    obtain ⟨k, _, h⟩ := tbind_ok_inv h
    obtain ⟨u, hck, h⟩ := tbind_ok_inv h
    cases h
    show (σ.storage.get r0.hroot).LiveAll (r0.path.append (Path.index it k))
    obtain ⟨y0, hy0, hin⟩ := Storage.checkIndex_some (TRes.ofOpt_ok hck)
    refine SVal.liveAll_append _ _ _ (SPath.resolveT_liveAll b h0) fun y hy => ?_
    have hyy : y = y0 := by
      have : (σ.storage.get r0.hroot).find r0.path = some y := by
        rw [SVal.find_eq_findM]; exact hy
      rw [show σ.storage.find r0 = (σ.storage.get r0.hroot).find r0.path from rfl, this] at hy0
      exact Option.some.inj hy0
    subst hyy
    cases it with
    | map =>
      rw [Path.index_map]
      cases y with
      | map m d => simp only [SVal.LiveAll]; split <;> trivial
    | arr a =>
      cases a with
      | dyn =>
        rw [Path.index_dyn]
        cases y with
        | array e sh hn =>
          change (if (k : PrimTy.uint.Denote).1.toNat < _ then some () else none) = _ at hin
          split at hin
          · rename_i hb
            simp only [SVal.LiveAll]
            exact ⟨hb, fun _ _ => trivial⟩
          · exact nomatch hin
      | fixed =>
        rw [Path.index_fixed]
        cases y with
        | fixed e => simp only [SVal.LiveAll]; exact fun _ _ => trivial

/-- A path resolves to live slots: an alias is live by the invariant. -/
theorem SPath.resolveT_liveAll : {T : Ty} → (b : SPath C Γ T) → ∀ {r : SRef C T},
    b.resolveT σ = .ok r → σ.storage.LiveAll r
  | _, .alias i, r, h => by
    have hi := TEnv.All.get i he
    simp only [SPath.resolveT] at h
    split at h
    · rename_i r' hr'
      cases h
      exact hi _ hr'
    · exact nomatch h
  | _, .loc l, _, h => Loc.resolveT_liveAll l h

end

end Resolve

/-- The storage value a source stores has clean tails. -/
theorem Src.valueT_ct {Γ : Ctx} {σ : State C Γ} {T : Ty} (hs : σ.storage.All cleanTailH) :
    (r : Src C Γ T) → {v : SVal T} → r.valueT σ = .ok v → v.All cleanTailH
  | .val _, v, h => by
    obtain ⟨x, _, h⟩ := tbind_ok_inv h
    cases h
    simp only [SVal.All]
  | .copy _ _, v, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    exact Storage.find_all hs (TRes.ofOpt_ok h)
  | .copyMem _, v, h => by
    obtain ⟨mv, _, h⟩ := tbind_ok_inv h
    cases h
    exact SVal.plain_ct (MVal.copyMToSt_plain σ.heap mv)
  | .fixedCopy _ shape hm, v, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨sv, _, h⟩ := tbind_ok_inv h
    cases h
    exact SVal.plain_ct (shape.apply_plain sv hm)

/-- An alias's right-hand side: clean tails, every live reference kept live,
and the reference it names live. -/
theorem ARhs.evalT_ct {Γ : Ctx} {σ : State C Γ} (hσ : CTInv σ) {R : RefTy} :
    (r : ARhs C Γ R) → {st : Storage C} → {ref : SRef C (.ref R)} →
      r.evalT σ = .ok (st, ref) →
      st.All cleanTailH ∧ σ.storage.Grows st ∧ st.LiveAll ref
  | .path p, st, ref, h => by
    obtain ⟨r0, h0, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hσ.1, Storage.Grows.refl _, SPath.resolveT_liveAll σ hσ.2 p h0⟩
  | .push b _, st, ref, h => by
    obtain ⟨r0, h0, h⟩ := tbind_ok_inv h
    split at h
    · exact nomatch h
    · obtain ⟨⟨st', k⟩, hst, h⟩ := tbind_ok_inv h
      cases h
      have hp := TRes.ofOpt_ok hst
      have hl := SPath.resolveT_liveAll σ hσ.2 b h0
      exact ⟨Storage.pushPlace_ct hσ.1 hl hp, Storage.pushPlace_grows hp,
        Storage.pushPlace_liveAll hl hp⟩

/-! ## Steps that keep the invariant -/

/-- A step keeps the invariant and, where `g` (an alias may be held around
it), every live reference live. -/
def CKeeps (g : Bool) {Γ Γ' : Ctx} (t : TStep C Γ Γ') : Prop :=
  ∀ (σ : State C Γ) (o : Out C σ.H Γ'), CTInv σ → t σ = .ok o →
    CTInv o.st ∧ (g = true → σ.storage.Grows o.st.storage)

/-- The invariant at one storage, as `RunInv` reads locals. -/
def liveInv (st : Storage C) : RunInv C where
  glob _ := True
  loc := aliasLive st
  loc_wk := @fun _ _ x t v h => aliasLive_wk x t v h

namespace CKeeps

variable {Γ : Ctx}

theorem weaken {g g' : Bool} {Γ' : Ctx} {t : TStep C Γ Γ'} (h : CKeeps g t)
    (hg : g' = true → g = true) : CKeeps g' t :=
  fun σ o hσ ht => ⟨(h σ o hσ ht).1, fun h' => (h σ o hσ ht).2 (hg h')⟩

theorem drop {g : Bool} {Δ Δ' : Ctx} {t : TStep C Γ Δ} (hf : CKeeps g t) (x : Ext Δ' Δ) :
    CKeeps g (fun σ => (t σ).map fun o => ⟨o.st.drop x, o.ext⟩) := by
  intro σ o hσ h
  obtain ⟨o₁, hr, rfl⟩ := tmap_ok_inv h
  exact ⟨(hf σ o₁ hσ hr).1.drop x, (hf σ o₁ hσ hr).2⟩

theorem seq {g : Bool} {Γ₁ Γ₂ : Ctx} {s : TStep C Γ Γ₁} {P : TStep C Γ₁ Γ₂} (hs : CKeeps g s)
    (hP : CKeeps g P) : CKeeps g (TRun.seq s P) := by
  intro σ o hσ h
  unfold TRun.seq at h
  split at h
  · rename_i o₁ ho₁
    obtain ⟨o₂, hp, rfl⟩ := tmap_ok_inv h
    have h1 := hs σ o₁ hσ ho₁
    have h2 := hP o₁.st o₂ h1.1 hp
    exact ⟨h2.1, fun hg => Storage.Grows.trans (h1.2 hg) (h2.2 hg)⟩
  · cases h

theorem nil {g : Bool} : CKeeps g (TRun.nil : TStep C Γ Γ) := by
  intro σ o hσ h
  cases h
  exact ⟨hσ, fun _ => Storage.Grows.refl _⟩

theorem ite {g : Bool} {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) {thn : TStep C Γ Γ₁}
    (h₂ : Ext Γ Γ₂) {els : TStep C Γ Γ₂} (hthn : CKeeps g thn) (hels : CKeeps g els) :
    CKeeps g (TRun.ite c h₁ thn h₂ els) := by
  intro σ o hσ h
  unfold TRun.ite at h
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
  split at h
  · exact hthn.drop h₁ σ o hσ h
  · exact hels.drop h₂ σ o hσ h

theorem block {g : Bool} {Γ₁ : Ctx} (x : Ext Γ Γ₁) {body : TStep C Γ Γ₁} (hb : CKeeps g body) :
    CKeeps g (TRun.block x body) :=
  hb.drop x

/-- A step that changes nothing it ends in. -/
theorem same {g : Bool} {t : TStep C Γ Γ}
    (ht : ∀ σ o, t σ = .ok o → o.st = σ) : CKeeps g t := by
  intro σ o hσ h
  have e := ht σ o h
  refine ⟨?_, fun _ => ?_⟩
  · rw [e]; exact hσ
  · rw [e]; exact Storage.Grows.refl _

theorem require {g : Bool} (c : Val C Γ .bool) : CKeeps g (TRun.require c) := by
  refine same fun σ o h => ?_
  unfold TRun.require at h
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
  split at h
  · cases h; rfl
  · cases h

theorem assert {g : Bool} (c : Val C Γ .bool) : CKeeps g (TRun.assert c) := by
  refine same fun σ o h => ?_
  unfold TRun.assert at h
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
  split at h
  · cases h; rfl
  · cases h

theorem halt {g : Bool} (e : THalt) :
    CKeeps g (fun _ : State C Γ => (.error e : TRes (Out C _ Γ))) :=
  fun _ _ _ h => nomatch h

theorem loop {g : Bool} {Γ₁ : Ctx} (c : Val C Γ .bool) (x : Ext Γ Γ₁) {body : TStep C Γ Γ₁}
    (hb : CKeeps g body) : CKeeps g (TRun.loop c x body) := by
  intro σ o hσ h
  unfold TRun.loop at h
  refine TLoop.run_induct
    (P := fun o : Out C σ.H Γ => CTInv o.st ∧ (g = true → σ.storage.Grows o.st.storage))
    (Q := fun r => ∀ o, r = .ok o → CTInv o.st ∧ (g = true → σ.storage.Grows o.st.storage))
    ⟨hσ, fun _ => Storage.Grows.refl _⟩ (fun τ h₁ => ?_) (fun _ h => nomatch h) _ h
  simp only [TLoop.step]
  rcases c.evalT τ.st with _ | b
  · exact fun _ h => nomatch h
  · cases b
    · exact fun _ h => by cases h; exact h₁
    · dsimp only
      cases hr : body τ.st with
      | error => exact fun _ h => nomatch h
      | ok τ' =>
        have h2 := hb τ.st τ' h₁.1 hr
        exact ⟨h2.1.drop x, fun hg => Storage.Grows.trans (h₁.2 hg) (h2.2 hg)⟩

end CKeeps

/-- A call's arguments are live: an alias argument resolves to live slots. -/
theorem Args.evalT_live {Γ : Ctx} (σ : State C Γ) (he : TEnv.All (aliasLive σ.storage) σ.env) :
    {ps : Ctx} → (as : Args C Γ ps) → {a : TEnv C σ.H ps} → Args.evalT σ as = .ok a →
      TEnv.All (aliasLive σ.storage) a
  | _, .nil, _, _ => trivial
  | _, .snoc as _ _ _, a, h => by
    obtain ⟨r, hr, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨trivial, Args.evalT_live σ he as hr⟩
  | _, .snocStorage as _ _ e, a, h => by
    obtain ⟨r, hr, h⟩ := tbind_ok_inv h
    obtain ⟨v, hv, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨fun r' hr' => by cases hr'; exact SPath.resolveT_liveAll σ he e hv,
      Args.evalT_live σ he as hr⟩
  | _, .snocMemory as _ _ _, a, h => by
    obtain ⟨r, hr, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨trivial, Args.evalT_live σ he as hr⟩

namespace CKeeps

variable {Γ : Ctx}

/-- **A call**: its body keeps the invariant, every live reference live
where the caller may hold an alias (`g`). -/
theorem call {g : Bool} {Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (x : Ext (rs ++ ps) Γf) {body : TStep C (rs ++ ps) Γf} (hb : CKeeps g body)
    (hg : Γ.hasAlias = true → g = true) : CKeeps g (TRun.call args ret x body) := by
  intro σ o hσ h
  unfold TRun.call at h
  obtain ⟨a, ha, h⟩ := tbind_ok_inv h
  dsimp only at h
  obtain ⟨o₂, hr, h⟩ := tbind_ok_inv h
  cases h
  have hA := Args.evalT_live σ hσ.2 args ha
  have h₁ : CTInv (ret.enterT (σ.withEnv a)).st := by
    refine ⟨by rw [CallRet.enterT_storage]; exact hσ.1, ?_⟩
    rw [CallRet.enterT_storage]
    exact RunInv.enterT_env (I := liveInv σ.storage) (fun _ _ _ => trivial)
      (fun _ _ _ => trivial) (fun _ _ _ h => nomatch h) ret (σ.withEnv a) hA
  have h₂ := hb _ o₂ h₁ hr
  have hst : (ret.enterT (σ.withEnv a)).st.storage = σ.storage := by
    rw [CallRet.enterT_storage]; rfl
  rw [hst] at h₂
  refine ⟨⟨h₂.1.1, ?_⟩, h₂.2⟩
  have hcaller : TEnv.All (aliasLive o₂.st.storage) σ.env := by
    cases ha' : Γ.hasAlias
    · exact env_noAlias _ ha' _
    · exact CTInv.env_grows (h₂.2 (hg ha')) hσ.2
  exact CallRet.leaveT_all (P := aliasLive o₂.st.storage) ret (env_wk_live _ hcaller)
    (TEnv.All.take rs (TEnv.All.drop x h₂.1.2))

end CKeeps

namespace CKeeps

variable {Γ : Ctx}

/-- **A `try`**: a self-call's frame and each clause keep the invariant. -/
theorem tryCall {g : Bool} {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (call : ExtCall C Γ)
    (rets : Binders ρ) (h₁ : Ext (ρ ++ Γ) Γ₁) {ok : TStep C (ρ ++ Γ) Γ₁}
    (h₂ : Ext Γ Γ₂) {err : TStep C Γ Γ₂} (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) {pnc : TStep C (κ ++ Γ) Γ₃}
    (h₄ : Ext Γ Γ₄) {other : TStep C Γ Γ₄} (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf)
    {sbody : TStep C (ρ ++ ps) Γf} (self : Bool)
    (hok : CKeeps g ok) (herr : CKeeps g err) (hpnc : CKeeps g pnc) (hoth : CKeeps g other)
    (hsb : CKeeps g sbody) (hg : Γ.hasAlias = true → g = true) :
    CKeeps g (TRun.tryCall call rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody self) := by
  intro σ o hσ h
  unfold TRun.tryCall at h
  have hvm : ∀ {H : HTy} {κ' : Ctx}, Ctx.ValMem κ' → ∀ (e : TEnv C H κ'),
      TEnv.All (aliasLive σ.storage) e :=
    fun hv e => TEnv.All.of_valMem (P := aliasLive σ.storage) (fun _ _ => trivial)
      (fun _ _ => trivial) hv e
  have hp : ∀ c, CTInv (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env)) :=
    fun _ => ⟨hσ.1, TEnv.All.append κ (hvm (CodeBinder.valMem code) _) hσ.2⟩
  split at h
  · cases h
  split at h
  · split at h
    · rename_i o₁ hc
      have h1 := CKeeps.call sargs (.rets rets) hs hsb hg σ o₁ hσ hc
      cases hr : ok o₁.st with
      | error => rw [hr] at h; cases h
      | ok o' =>
        rw [hr] at h; cases h
        have h2 := hok _ o' h1.1 hr
        exact ⟨h2.1.drop _, fun hg' => Storage.Grows.trans (h1.2 hg') (h2.2 hg')⟩
    · exact hoth.drop h₄ σ o hσ h
    · split at h
      · exact herr.drop h₂ σ o hσ h
      · split at h
        · exact hpnc.drop ((Ext.append Γ κ).trans h₃) _ o (hp _) h
        · exact hoth.drop h₄ σ o hσ h
    · exact hpnc.drop ((Ext.append Γ κ).trans h₃) _ o (hp _) h
    · cases h
  split at h
  · cases h
  · obtain ⟨⟨r, rest⟩, _, h⟩ := tbind_ok_inv h
    exact hok.drop ((Ext.append Γ ρ).trans h₁) (σ.withEnv (TEnv.append ρ r σ.env)) o
      ⟨hσ.1, TEnv.All.append ρ (hvm (Binders.valMem rets) _) hσ.2⟩ h
  · exact herr.drop h₂ σ o hσ h
  · exact hpnc.drop ((Ext.append Γ κ).trans h₃) _ o (hp _) h
  · exact hoth.drop h₄ σ o hσ h

end CKeeps

/-- A `new` array stored, not kept in memory. -/
def NewLhs.isStore {Γ : Ctx} {R : RefTy} : NewLhs C Γ R → Bool
  | .store _ => true
  | .mem _ => false

/-! ## The statements without sub-programs -/

section Leaves

variable {Γ : Ctx}

/-- A step that only writes the storage: clean tails, and every live
reference live where it grows. -/
theorem CKeeps.ofStorage {g : Bool} {t : TStep C Γ Γ}
    (ht : ∀ σ o, CTInv σ → t σ = .ok o → ∃ st, o.st = σ.withStorage st ∧ st.All cleanTailH ∧
      (g = true ∨ Γ.hasAlias = true → σ.storage.Grows st)) : CKeeps g t := by
  intro σ o hσ h
  obtain ⟨st, e, hs, hg⟩ := ht σ o hσ h
  rw [e]
  exact ⟨hσ.withStorage hs fun ha => hg (Or.inr ha), fun hg' => hg (Or.inl hg')⟩

theorem ckeeps_assign {g : Bool} {T : Ty} (l : Loc C Γ T) (r : Src C Γ T)
    (hT : T.isPrimitive = true ∨ (g = false ∧ Γ.hasAlias = false)) :
    CKeeps g (TRun.assign l r) := by
  refine CKeeps.ofStorage fun σ o hσ h => ?_
  unfold TRun.assign at h
  obtain ⟨sv, hsv, h⟩ := tbind_ok_inv h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  refine ⟨st, rfl, Storage.write_ct hσ.1 (Src.valueT_ct hσ.1 r hsv)
    (Loc.resolveT_liveAll σ hσ.2 l href) (TRes.ofOpt_ok hst), fun hg => ?_⟩
  rcases hT with hT | ⟨hg', ha⟩
  · cases T with
    | prim q => exact Storage.write_prim_grows (TRes.ofOpt_ok hst)
    | ref _ => exact nomatch hT
  · rcases hg with hg | hg
    · rw [hg'] at hg; exact nomatch hg
    · rw [ha] at hg; exact nomatch hg

theorem ckeeps_rebind {g : Bool} {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) :
    CKeeps g (TRun.rebind i r) := by
  intro σ o hσ h
  unfold TRun.rebind at h
  obtain ⟨⟨st, ref⟩, he, h⟩ := tbind_ok_inv h
  cases h
  obtain ⟨hs, hg, hl⟩ := ARhs.evalT_ct hσ r he
  refine ⟨(hσ.withStorage hs fun _ => hg).setLocal i fun r' hr' => ?_, fun _ => hg⟩
  cases hr'; exact hl

theorem ckeeps_assignLocal {g : Bool} {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) :
    CKeeps g (TRun.assignLocal i r) := by
  intro σ o hσ h
  unfold TRun.assignLocal at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨hσ.setLocal i trivial, fun _ => Storage.Grows.refl _⟩

theorem ckeeps_declLocal {g : Bool} (p : PrimTy) (init : Option (Val C Γ p)) :
    CKeeps g (TRun.declLocal p init) := by
  intro σ o hσ h
  unfold TRun.declLocal at h
  cases init with
  | none => cases h; exact ⟨hσ.push trivial, fun _ => Storage.Grows.refl _⟩
  | some e =>
    dsimp only at h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hσ.push trivial, fun _ => Storage.Grows.refl _⟩

theorem ckeeps_declStorage {g : Bool} (R : RefTy) (init : Option (ARhs C Γ R)) :
    CKeeps g (TRun.declStorage R init) := by
  intro σ o hσ h
  unfold TRun.declStorage at h
  cases init with
  | none =>
    cases h
    exact ⟨hσ.push (fun _ h => nomatch h), fun _ => Storage.Grows.refl _⟩
  | some r =>
    obtain ⟨⟨st, ref⟩, he, h⟩ := tbind_ok_inv h
    cases h
    obtain ⟨hs, hg, hl⟩ := ARhs.evalT_ct hσ r he
    refine ⟨(hσ.withStorage hs fun _ => hg).push fun r' hr' => ?_, fun _ => hg⟩
    cases hr'; exact hl

/-- A word saved at a live reference. -/
theorem opStoreT_ct {σ : State C Γ} (hσ : CTInv σ) (op : BinOp) {p : PrimTy} {r : SRef C (.prim p)}
    (hl : σ.storage.LiveAll r) (v : p.Denote) {o : Out C σ.H Γ} (h : opStoreT σ op r v = .ok o) :
    CTInv o.st ∧ σ.storage.Grows o.st.storage := by
  unfold opStoreT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  have hg : σ.storage.Grows st := Storage.save_prim_grows (TRes.ofOpt_ok hst)
  exact ⟨hσ.withStorage (Storage.save_ct hσ.1 (by simp only [SVal.All]) hl (TRes.ofOpt_ok hst))
    fun _ => hg, hg⟩

theorem bumpStoreT_ct {σ : State C Γ} (hσ : CTInv σ) (op : IncDec) {p : PrimTy}
    {r : SRef C (.prim p)} (hl : σ.storage.LiveAll r) {o : Out C σ.H Γ} {w : p.Denote}
    (h : bumpStoreT σ op r = .ok (o, w)) : CTInv o.st ∧ σ.storage.Grows o.st.storage := by
  unfold bumpStoreT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  have hg : σ.storage.Grows st := Storage.save_prim_grows (TRes.ofOpt_ok hst)
  exact ⟨hσ.withStorage (Storage.save_ct hσ.1 (by simp only [SVal.All]) hl (TRes.ofOpt_ok hst))
    fun _ => hg, hg⟩

theorem opMemT_ct {σ : State C Γ} (hσ : CTInv σ) (op : BinOp) {p : PrimTy}
    (a : MAddr σ.H (.prim p)) (v : p.Denote) {o : Out C σ.H Γ} (h : opMemT σ op a v = .ok o) :
    CTInv o.st ∧ σ.storage.Grows o.st.storage := by
  unfold opMemT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨hσ, Storage.Grows.refl _⟩

theorem bumpMemT_ct {σ : State C Γ} (hσ : CTInv σ) (op : IncDec) {p : PrimTy}
    (a : MAddr σ.H (.prim p)) {o : Out C σ.H Γ} {w : p.Denote} (h : bumpMemT σ op a = .ok (o, w)) :
    CTInv o.st ∧ σ.storage.Grows o.st.storage := by
  unfold bumpMemT at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨hσ, Storage.Grows.refl _⟩

theorem OpLoc.storeT_ct {σ : State C Γ} (hσ : CTInv σ) (op : BinOp) :
    {p : PrimTy} → (l : OpLoc C Γ p) → (v : p.Denote) → {o : Out C σ.H Γ} →
      l.storeT σ op v = .ok o → CTInv o.st ∧ σ.storage.Grows o.st.storage
  | _, .local i, _, o, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hσ.setLocal i trivial, Storage.Grows.refl _⟩
  | _, .root r hr, v, o, h =>
    opStoreT_ct hσ op (r := SRef.ofRoot r hr) (SVal.liveAll_nil _) v h
  | _, .field b f hf, v, o, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact opStoreT_ct hσ op (Loc.resolveT_liveAll σ hσ.2 _ href) v h
  | _, .index it b i, v, o, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact opStoreT_ct hσ op (Loc.resolveT_liveAll σ hσ.2 _ href) v h
  | _, .mfield .., v, o, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact opMemT_ct hσ op a v h
  | _, .mindex .., v, o, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact opMemT_ct hσ op a v h

theorem OpLoc.bumpT_ct {σ : State C Γ} (hσ : CTInv σ) (op : IncDec) :
    {p : PrimTy} → (l : OpLoc C Γ p) → {o : Out C σ.H Γ} → {w : p.Denote} →
      l.bumpT σ op = .ok (o, w) → CTInv o.st ∧ σ.storage.Grows o.st.storage
  | _, .local i, o, w, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hσ.setLocal i trivial, Storage.Grows.refl _⟩
  | _, .root r hr, o, w, h =>
    bumpStoreT_ct hσ op (r := SRef.ofRoot r hr) (SVal.liveAll_nil _) h
  | _, .field b f hf, o, w, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact bumpStoreT_ct hσ op (Loc.resolveT_liveAll σ hσ.2 _ href) h
  | _, .index it b i, o, w, h => by
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    exact bumpStoreT_ct hσ op (Loc.resolveT_liveAll σ hσ.2 _ href) h
  | _, .mfield .., o, w, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact bumpMemT_ct hσ op a h
  | _, .mindex .., o, w, h => by
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    exact bumpMemT_ct hσ op a h

theorem ckeeps_opAssign {g : Bool} {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) :
    CKeeps g (TRun.opAssign op l r) := by
  intro σ o hσ h
  unfold TRun.opAssign at h
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
  have := OpLoc.storeT_ct hσ op l v h
  exact ⟨this.1, fun _ => this.2⟩

theorem ckeeps_incDec {g : Bool} {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) :
    CKeeps g (TRun.incDec op l) := by
  intro σ o hσ h
  unfold TRun.incDec at h
  obtain ⟨⟨o', w⟩, hb, h⟩ := tbind_ok_inv h
  cases h
  have := OpLoc.bumpT_ct hσ op l hb
  exact ⟨this.1, fun _ => this.2⟩

theorem ckeeps_assignIncDec {g : Bool} {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (l : OpLoc C Γ p) : CKeeps g (TRun.assignIncDec i op l) := by
  intro σ o hσ h
  unfold TRun.assignIncDec at h
  obtain ⟨⟨o', w⟩, hb, h⟩ := tbind_ok_inv h
  cases h
  have := OpLoc.bumpT_ct hσ op l hb
  exact ⟨this.1.setLocal i trivial, fun _ => this.2⟩

theorem ckeeps_push {g : Bool} {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    CKeeps g (TRun.push b v) := by
  refine CKeeps.ofStorage fun σ o hσ h => ?_
  unfold TRun.push at h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨x, hx, h⟩ : ∃ x : Option (SVal E), (∀ x0, x = some x0 → x0.All cleanTailH) ∧
      (if σ.storage.full ref = true then Except.error THalt.exhausted
       else do
        let st ← TRes.ofOpt (σ.storage.push ref fun slot => some (x.getD slot))
        pure ({ st := σ.withStorage st, ext := List.prefix_refl _ } : Out C σ.H Γ)) = .ok o := by
    cases v with
    | none => exact ⟨none, (fun _ h => nomatch h), h⟩
    | some r =>
      dsimp only at h
      obtain ⟨sv, hsv, h⟩ := tbind_ok_inv h
      refine ⟨some sv.strip, (fun x0 hx0 => ?_), h⟩
      cases hx0
      exact SVal.strip_all cleanTailH_stripOK (Src.valueT_ct hσ.1 r hsv)
  split at h
  · exact nomatch h
  · obtain ⟨st, hst, h⟩ := tbind_ok_inv h
    cases h
    refine ⟨st, rfl, Storage.push_ct hσ.1 (SPath.resolveT_liveAll σ hσ.2 b href)
      (fun s y hs hy => ?_) (TRes.ofOpt_ok hst), fun _ => Storage.push_grows (TRes.ofOpt_ok hst)⟩
    cases hy
    cases x with
    | none => exact hs
    | some x0 => exact hx x0 rfl

theorem ckeeps_assignLocalPush {g : Bool} {p : PrimTy} (i : Idx Γ (.val p))
    (b : SPath C Γ (.array (.prim p))) : CKeeps g (TRun.assignLocalPush i b) := by
  intro σ o hσ h
  unfold TRun.assignLocalPush at h
  obtain ⟨o', ho', h⟩ := tbind_ok_inv h
  cases h
  have := ckeeps_push (g := true) b none σ o' hσ ho'
  exact ⟨this.1.setLocal i trivial, fun _ => this.2 rfl⟩

theorem ckeeps_pushOpAssign {g : Bool} {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (r : Val C Γ p) : CKeeps g (TRun.pushOpAssign op b r) := by
  intro σ o hσ h
  unfold TRun.pushOpAssign at h
  obtain ⟨v, _, h⟩ := tbind_ok_inv h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  split at h
  · cases h
  · obtain ⟨⟨st, k⟩, hs, h⟩ := tbind_ok_inv h
    have hs' : σ.storage.pushPlace ref = some (st, k) := TRes.ofOpt_ok hs
    have hl := SPath.resolveT_liveAll σ hσ.2 b href
    have hg : σ.storage.Grows st := Storage.pushPlace_grows hs'
    have hst := hσ.withStorage (Storage.pushPlace_ct hσ.1 hl hs') fun _ => hg
    have := opStoreT_ct hst op (Storage.pushPlace_liveAll hl hs') v h
    exact ⟨this.1, fun _ => Storage.Grows.trans hg this.2⟩

theorem ckeeps_pushIncDec {g : Bool} {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p))) :
    CKeeps g (TRun.pushIncDec op b) := by
  intro σ o hσ h
  unfold TRun.pushIncDec at h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  split at h
  · cases h
  · obtain ⟨⟨st, k⟩, hs, h⟩ := tbind_ok_inv h
    obtain ⟨⟨o', value⟩, hb, h⟩ := tbind_ok_inv h
    cases h
    have hs' : σ.storage.pushPlace ref = some (st, k) := TRes.ofOpt_ok hs
    have hl := SPath.resolveT_liveAll σ hσ.2 b href
    have hg : σ.storage.Grows st := Storage.pushPlace_grows hs'
    have hst := hσ.withStorage (Storage.pushPlace_ct hσ.1 hl hs') fun _ => hg
    have := bumpStoreT_ct hst op (Storage.pushPlace_liveAll hl hs') hb
    exact ⟨this.1, fun _ => Storage.Grows.trans hg this.2⟩

/-- A `pop`: clean tails always, every live reference kept live where its
elements are words. -/
theorem pop_ct {σ : State C Γ} (hσ : CTInv σ) {E : Ty} (b : SPath C Γ (.array E))
    {o : Out C σ.H Γ} (h : TRun.pop b σ = .ok o) :
    ∃ st, o.st = σ.withStorage st ∧ st.All cleanTailH ∧
      (E.isPrimitive = true → σ.storage.Grows st) := by
  unfold TRun.pop at h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  refine ⟨st, rfl, Storage.pop_ct hσ.1 (SPath.resolveT_liveAll σ hσ.2 b href) id
    (TRes.ofOpt_ok hst), fun hE => ?_⟩
  cases E with
  | prim q => exact Storage.pop_words_grows (TRes.ofOpt_ok hst)
  | ref _ => exact nomatch hE

theorem ckeeps_pop {g : Bool} {E : Ty} (b : SPath C Γ (.array E))
    (hE : E.isPrimitive = true ∨ (g = false ∧ Γ.hasAlias = false)) : CKeeps g (TRun.pop b) := by
  refine CKeeps.ofStorage fun σ o hσ h => ?_
  obtain ⟨st, e, hs, hg⟩ := pop_ct hσ b h
  refine ⟨st, e, hs, fun hga => ?_⟩
  rcases hE with hE | ⟨hg', ha⟩
  · exact hg hE
  · rcases hga with h' | h'
    · rw [hg'] at h'; exact nomatch h'
    · rw [ha] at h'; exact nomatch h'

theorem ckeeps_transfer {g : Bool} (r a : Val C Γ .uint) : CKeeps g (TRun.transfer r a) := by
  intro σ o hσ h
  unfold TRun.transfer at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨hσ, fun _ => Storage.Grows.refl _⟩

theorem ckeeps_send {g : Bool} (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) :
    CKeeps g (TRun.send pv r a) := by
  intro σ o hσ h
  unfold TRun.send at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  unfold sendT
  split
  · exact ⟨CTInv.setLocal (σ := σ.pay _ _) hσ pv trivial, fun _ => Storage.Grows.refl _⟩
  · exact ⟨hσ.setLocal pv trivial, fun _ => Storage.Grows.refl _⟩
  · exact ⟨hσ.setLocal pv trivial, fun _ => Storage.Grows.refl _⟩

theorem MRhs.evalT_ct {σ : State C Γ} (hσ : CTInv σ) {R : RefTy} :
    (r : MRhs C Γ R) → {g : Grew C Γ σ.H (HRef · R)} → r.evalT σ = .ok g →
      CTInv g.st ∧ g.st.storage = σ.storage
  | .alias _, g, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hσ, rfl⟩
  | .copy _ _, g, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hσ.adopt _, rfl⟩
  | .newArr _ _, g, h => by
    cases h
    exact ⟨hσ.adopt _, rfl⟩

theorem ckeeps_declMem {g : Bool} (R : RefTy) (init : Option (MRhs C Γ R))
    (hm : (Ty.ref R).mapFree = true) : CKeeps g (TRun.declMem R init hm) := by
  intro σ o hσ h
  unfold TRun.declMem at h
  cases init with
  | none => cases h; exact ⟨(hσ.adopt _).push trivial, fun _ => Storage.Grows.refl _⟩
  | some r =>
    obtain ⟨g', hg, h⟩ := tbind_ok_inv h
    cases h
    obtain ⟨h1, h2⟩ := MRhs.evalT_ct hσ r hg
    refine ⟨h1.push trivial, fun _ => ?_⟩
    show σ.storage.Grows g'.st.storage
    rw [h2]; exact Storage.Grows.refl _

theorem ckeeps_rebindMem {g : Bool} {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) :
    CKeeps g (TRun.rebindMem i r) := by
  intro σ o hσ h
  unfold TRun.rebindMem at h
  obtain ⟨g', hg, h⟩ := tbind_ok_inv h
  cases h
  obtain ⟨h1, h2⟩ := MRhs.evalT_ct hσ r hg
  refine ⟨h1.setLocal i trivial, fun _ => ?_⟩
  show σ.storage.Grows g'.st.storage
  rw [h2]; exact Storage.Grows.refl _

theorem ckeeps_assignFromMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R))
    (ha : Γ.hasAlias = false) : CKeeps false (TRun.assignFromMem l p) := by
  refine CKeeps.ofStorage fun σ o hσ h => ?_
  unfold TRun.assignFromMem at h
  obtain ⟨m, _, h⟩ := tbind_ok_inv h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  refine ⟨st, rfl, Storage.write_ct hσ.1 (SVal.plain_ct (MVal.copyMToSt_plain σ.heap m))
    (Loc.resolveT_liveAll σ hσ.2 l href) (TRes.ofOpt_ok hst), fun h' => ?_⟩
  rcases h' with h' | h'
  · exact nomatch h'
  · rw [ha] at h'; exact nomatch h'

theorem ckeeps_assignMem {g : Bool} {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    CKeeps g (TRun.assignMem l r) := by
  intro σ o hσ h
  unfold TRun.assignMem at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨hσ, fun _ => Storage.Grows.refl _⟩

theorem ckeeps_litWritesT {g : Bool} {Γ₁ : Ctx} {k : TStep C (.mem bytesR :: Γ) Γ₁}
    (hk : CKeeps g k) : (bs : List UInt8) → (i : Nat) → CKeeps g (TRun.litWritesT bs i k)
  | [], _ => hk
  | b :: bs, i => by
    unfold TRun.litWritesT
    split
    · exact CKeeps.seq (ckeeps_assignMem _ _) (ckeeps_litWritesT hk bs (i + 1))
    · exact hk

theorem ckeeps_litBytesT {g : Bool} {Γ₁ : Ctx} {k : TStep C (.mem bytesR :: Γ) Γ₁}
    (hk : CKeeps g k) (bs : List UInt8) : CKeeps g (TRun.litBytesT bs k) := by
  unfold TRun.litBytesT
  split
  · exact CKeeps.seq (ckeeps_declMem _ _ _) (ckeeps_litWritesT hk bs 0)
  · exact CKeeps.seq (ckeeps_declMem _ _ _) hk

/-- A `catch` clause binding the data keeps clean tails as its body does:
the data is a fresh memory object, the callee's run read for its data only. -/
theorem ckeeps_catchData {g : Bool} {ρ ps Γf Γ₁ : Ctx} (c : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : TStep C (ρ ++ ps) Γf) (self : Bool)
    (kind : CatchKind) (h₁ : Ext (.mem bytesR :: Γ) Γ₁) {body : TStep C (.mem bytesR :: Γ) Γ₁}
    (hb : CKeeps g body) : CKeeps g (TRun.catchData c rets sargs hs sbody self kind h₁ body) := by
  intro σ o hσ h
  unfold TRun.catchData at h
  obtain ⟨d, _, h⟩ := tbind_ok_inv h
  split at h
  · cases h
  · exact (ckeeps_litBytesT hb _).drop _ σ o hσ h

/-- A revert with data ends in no state. -/
theorem ckeeps_revertData {g : Bool} (d : List (RevPart C Γ)) : CKeeps g (TRun.revertData d) := by
  intro σ o _ h
  unfold TRun.revertData at h
  obtain ⟨_, _, h⟩ := tbind_ok_inv h
  cases h

theorem ckeeps_delete {g : Bool} {T : Ty} (l : Loc C Γ T)
    (hT : T.isPrimitive = true ∨ (g = false ∧ Γ.hasAlias = false)) :
    CKeeps g (TRun.delete l) := by
  refine CKeeps.ofStorage fun σ o hσ h => ?_
  unfold TRun.delete at h
  obtain ⟨ref, href, h⟩ := tbind_ok_inv h
  obtain ⟨st, hst, h⟩ := tbind_ok_inv h
  cases h
  refine ⟨st, rfl, Storage.delete_ct hσ.1 (Loc.resolveT_liveAll σ hσ.2 l href)
    (TRes.ofOpt_ok hst), fun hg => ?_⟩
  rcases hT with hT | ⟨hg', ha⟩
  · cases T with
    | prim q => exact Storage.delete_prim_grows (TRes.ofOpt_ok hst)
    | ref _ => exact nomatch hT
  · rcases hg with hg | hg
    · rw [hg'] at hg; exact nomatch hg
    · rw [ha] at hg; exact nomatch hg

theorem clearT_ct {σ : State C Γ} (hσ : CTInv σ) :
    {T : Ty} → (a : MAddr σ.H T) → (hm : T.mapFree = true) → {o : Out C σ.H Γ} →
      TRun.clearT σ a hm = .ok o → CTInv o.st ∧ σ.storage.Grows o.st.storage
  | .prim _, _, _, o, h => by
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hσ, Storage.Grows.refl _⟩
  | .ref R, a, hm, o, h => by
    simp only [TRun.clearT] at h
    split at h
    · cases h
      exact ⟨hσ.adopt _, Storage.Grows.refl _⟩
    · exact nomatch h

theorem ckeeps_deleteMem {g : Bool} {T : Ty} (p : MPath C Γ T) : CKeeps g (TRun.deleteMem p) := by
  intro σ o hσ h
  unfold TRun.deleteMem at h
  cases p with
  | var i _ => cases h; exact ⟨(hσ.adopt _).setLocal i trivial, fun _ => Storage.Grows.refl _⟩
  | loc l =>
    obtain ⟨a, _, h⟩ := tbind_ok_inv h
    have := clearT_ct hσ a l.mapFree h
    exact ⟨this.1, fun _ => this.2⟩

theorem ckeeps_assignNew {g : Bool} {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (hn : R.newArrOk = true) (hs : l.isStore = false ∨ (g = false ∧ Γ.hasAlias = false)) :
    CKeeps g (TRun.assignNew l n hn) := by
  intro σ o hσ h
  unfold TRun.assignNew at h
  have hg : CTInv
      (σ.copyStToMG (newArrT R (n.evalT σ) hn) (RefTy.mapFree_of_newArrOk hn)).st :=
    hσ.adopt _
  cases l with
  | store l =>
    obtain ⟨ref, href, h⟩ := tbind_ok_inv h
    obtain ⟨st, hst, h⟩ := tbind_ok_inv h
    cases h
    rcases hs with hs | ⟨hg', ha⟩
    · exact nomatch hs
    · subst hg'
      refine ⟨hg.withStorage (Storage.write_ct hg.1
        (SVal.plain_ct (MVal.copyMToSt_plain _ _))
        (Loc.resolveT_liveAll _ hg.2 l href) (TRes.ofOpt_ok hst)) fun h' => ?_, nofun⟩
      rw [ha] at h'; exact nomatch h'
  | mem l =>
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    obtain ⟨_, _, h⟩ := tbind_ok_inv h
    cases h
    exact ⟨hg, fun _ => Storage.Grows.refl _⟩

end Leaves

/-! ## The check -/

/-- A receiver's `push`. -/
def ReceiverOp.isPush {Γ : Ctx} {E : Ty} : ReceiverOp C Γ E → Bool
  | .push .. => true
  | .pop => false

mutual

/-- **Exposes nothing**, from a context where a caller may hold an alias
(`outer`): a statement that may shrink an array of references (an
assignment or a `delete` of a reference, a copy out of memory, a `pop` of
references) is taken only where no alias is in scope, here or in a caller,
so no alias is ever left past a live end.  A recursive call is not
unfolded: it fails the check. -/
def Stmt.ctSafe : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool → Bool
  | Γ, _, s, outer =>
    let g := outer || Γ.hasAlias
    Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := @fun _ T _ _ => T.isPrimitive || !g) (rebind := fun _ _ => true)
    (assignLocal := fun _ _ => true)
    (declLocal := fun _ _ _ => true) (declStorage := fun _ _ _ => true)
    (opAssign := fun _ _ _ _ _ => true) (incDec := fun _ _ _ => true)
    (assignIncDec := fun _ _ _ _ _ => true) (assignLocalPush := fun _ _ => true)
    (pushOpAssign := fun _ _ _ _ _ => true) (pushIncDec := fun _ _ _ => true)
    (push := fun _ _ _ => true) (pop := @fun _ E _ => E.isPrimitive || !g)
    (transfer := fun _ _ => true) (send := fun _ _ _ _ => true)
    (declMem := fun _ _ _ _ _ => true) (rebindMem := fun _ _ => true)
    (assignFromMem := fun _ _ => !g) (assignMem := fun _ _ => true)
    (delete := @fun _ T _ => T.isPrimitive || !g) (deleteMem := fun _ _ => true)
    (assignNew := fun l _ _ => !l.isStore || !g)
    (ite := fun _ thn els => Prog.ctSafe thn outer && Prog.ctSafe els outer)
    (require := fun _ => true) (assert := fun _ => true) (revert := true) (assumeFalse := true)
    (call := fun _ _ _ body => Prog.ctSafe body g)
    (callReceiver := @fun _ _ _ E _ _ _ body op =>
      Prog.ctSafe body g && (op.isPush || E.isPrimitive || !g))
    (callReceiverPush := fun _ _ _ body code _ => Prog.ctSafe body g && Prog.ctSafe code true)
    (tryCall := fun _ _ ok err _ pnc other _ sbody _ =>
      Prog.ctSafe ok outer && Prog.ctSafe err outer && Prog.ctSafe pnc outer &&
        Prog.ctSafe other outer && Prog.ctSafe sbody g)
    (callRec := fun _ _ _ _ _ => false)
    (loop := fun _ _ body => Prog.ctSafe body outer) (block := fun body => Prog.ctSafe body outer)
    (revertData := fun _ => true)
    (catchData := fun _ _ _ _ _ _ _ body => Prog.ctSafe body outer)
  termination_by structural _ _ s => s

def Prog.ctSafe : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool → Bool
  | _, _, P, outer => Prog.casesOn (motive_2 := fun _ _ _ => Bool) P true
      (fun s P => Stmt.ctSafe s outer && Prog.ctSafe P outer)
  termination_by structural _ _ P => P

end

/-- **A program that exposes nothing**: run where nobody holds an alias. -/
def Prog.exposesNone {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Bool := P.ctSafe false

theorem ctSafe_or {a o h : Bool} (H : (a || !(o || h)) = true) :
    a = true ∨ ((o || h) = false ∧ h = false) := by
  cases a <;> cases o <;> cases h <;> simp_all

/-! ## Receivers -/

section Receivers

variable {Γ : Ctx}

theorem ckeeps_callReceiver {g : Bool} {ps Γf : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (h : Ext ([.alias (.array E)] ++ ps) Γf) {body : TStep C ([.alias (.array E)] ++ ps) Γf}
    (op : ReceiverOp C Γ E) (hb : CKeeps g body) (hg : Γ.hasAlias = true → g = true)
    (hop : op.isPush = true ∨ E.isPrimitive = true ∨ g = false) :
    CKeeps g (TRun.callReceiver args r h body op) := by
  intro σ o hσ hr
  rw [TRun.callReceiver_eq_seq] at hr
  refine CKeeps.seq (CKeeps.call args (.storage _ r) h hb hg) ?_ σ o hσ hr
  cases op with
  | push v _ =>
    exact CKeeps.weaken ((ckeeps_push (g := true) (.alias .here)
      (v.map (·.wk (.drop .refl)))).drop (.push .refl)) fun _ => rfl
  | pop =>
    rcases hop with hop | hop | hop
    · exact nomatch hop
    · exact CKeeps.weaken ((ckeeps_pop (g := true) (.alias .here) (Or.inl hop)).drop
        (.push .refl)) fun _ => rfl
    · subst hop
      intro τ o' hτ ho'
      obtain ⟨o₁, hr₁, rfl⟩ := tmap_ok_inv ho'
      obtain ⟨st, e, hs, _⟩ := pop_ct hτ (.alias .here) hr₁
      have ha : Γ.hasAlias = false := by
        cases ha : Γ.hasAlias
        · rfl
        · exact absurd (hg ha) (by simp only [Bool.false_eq_true, not_false_eq_true])
      refine ⟨⟨?_, env_noAlias _ ha _⟩, nofun⟩
      show (o₁.st.drop _).storage.All cleanTailH
      rw [e]; exact hs

theorem ckeeps_callReceiverPush {g : Bool} {ps Γf Γv : Ctx} {E : Ty} (args : Args C Γ ps)
    (r : Var) (hb : Ext ([.alias (.array E)] ++ ps) Γf)
    {body : TStep C ([.alias (.array E)] ++ ps) Γf} (he : Ext Γ Γv) {code : TStep C Γ Γv}
    (value : Src C Γv E) (hbody : CKeeps g body) (hcode : CKeeps true code)
    (hg : Γ.hasAlias = true → g = true) :
    CKeeps g (TRun.callReceiverPush args r hb body he code value) := by
  intro σ o hσ hr
  rw [TRun.callReceiverPush_eq_seq] at hr
  refine CKeeps.seq (CKeeps.call args (.storage _ r) hb hbody hg) ?_ σ o hσ hr
  intro τ v hτ hv
  unfold TRun.afterReceiverPrefix at hv
  obtain ⟨ref, href, hv⟩ := tbind_ok_inv hv
  have hl : τ.storage.LiveAll ref := SPath.resolveT_liveAll τ hτ.2 (.alias .here) href
  unfold TRun.pushAfterPrefix at hv
  obtain ⟨a, ha, hv⟩ := tbind_ok_inv hv
  have hτ' : CTInv (τ.drop (.push .refl)) := hτ.drop _
  have h1 := hcode _ a hτ' ha
  have hl' : a.st.storage.LiveAll ref := h1.2 rfl ref hl
  obtain ⟨w, hw, hv⟩ := tbind_ok_inv hv
  split at hv
  · exact nomatch hv
  · obtain ⟨st, hst, hv⟩ := tbind_ok_inv hv
    cases hv
    have hst' := TRes.ofOpt_ok hst
    have hgr : a.st.storage.Grows st := Storage.push_grows hst'
    have hx : w.strip.All cleanTailH :=
      SVal.strip_all cleanTailH_stripOK (Src.valueT_ct h1.1.1 value hw)
    refine ⟨(h1.1.withStorage (Storage.push_ct h1.1.1 hl' (fun _ y _ hy => by
      cases hy; exact hx) hst') fun _ => hgr).drop he, fun _ => ?_⟩
    exact Storage.Grows.trans (h1.2 rfl) hgr

end Receivers

/-! ## Every statement that passes the check keeps the invariant -/

mutual

/-- **A statement that exposes nothing keeps clean tails**, its aliases
live, and every live reference live where an alias may be held around it. -/
theorem Stmt.keeps_ct : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → (outer : Bool) →
    s.ctSafe outer = true → CKeeps (outer || Γ.hasAlias) (Stmt.runR s)
  | _, _, .assign l r, _, h => ckeeps_assign l r (ctSafe_or h)
  | _, _, .rebind i r, _, _ => ckeeps_rebind i r
  | _, _, .assignLocal i r, _, _ => ckeeps_assignLocal i r
  | _, _, .declLocal p _ init, _, _ => ckeeps_declLocal p init
  | _, _, .declStorage R _ init, _, _ => ckeeps_declStorage R init
  | _, _, .opAssign op _ _ l r, _, _ => ckeeps_opAssign op l r
  | _, _, .incDec op _ l, _, _ => ckeeps_incDec op l
  | _, _, .pushOpAssign op _ _ b r, _, _ => ckeeps_pushOpAssign op b r
  | _, _, .pushIncDec op _ b, _, _ => ckeeps_pushIncDec op b
  | _, _, .assignIncDec i op _ l _, _, _ => ckeeps_assignIncDec i op l
  | _, _, .assignLocalPush i b, _, _ => ckeeps_assignLocalPush i b
  | _, _, .push b v _, _, _ => ckeeps_push b v
  | _, _, .pop b, _, h => ckeeps_pop b (ctSafe_or h)
  | _, _, .transfer r a, _, _ => ckeeps_transfer r a
  | _, _, .send pv r a _, _, _ => ckeeps_send pv r a
  | _, _, .declMem R _ init _ hm, _, _ => ckeeps_declMem R init hm
  | _, _, .rebindMem i r, _, _ => ckeeps_rebindMem i r
  | Γ, _, .assignFromMem l p, outer, h => by
    have h' : (outer || Γ.hasAlias) = false := by
      simpa only [Stmt.ctSafe, Bool.not_eq_eq_eq_not, Bool.not_true] using h
    rw [h']
    exact ckeeps_assignFromMem l p (by cases outer <;> simp_all)
  | _, _, .assignMem l r, _, _ => ckeeps_assignMem l r
  | _, _, .delete l, _, h => ckeeps_delete l (ctSafe_or h)
  | _, _, .deleteMem p _, _, _ => ckeeps_deleteMem p
  | Γ, _, .assignNew l n hn, outer, h => by
    refine ckeeps_assignNew l n hn ?_
    have h' : (!l.isStore || !(outer || Γ.hasAlias)) = true := h
    cases hl : l.isStore <;> cases outer <;> cases ha : Γ.hasAlias <;> simp_all
  | Γ, _, .ite c thn els, outer, h => by
    have h' : (Prog.ctSafe thn outer && Prog.ctSafe els outer) = true := h
    rw [Bool.and_eq_true] at h'
    exact CKeeps.ite c thn.ext els.ext (Prog.keeps_ct thn outer h'.1)
      (Prog.keeps_ct els outer h'.2)
  | _, _, .require c, _, _ => CKeeps.require c
  | _, _, .assert c, _, _ => CKeeps.assert c
  | _, _, .revert, _, _ => CKeeps.halt .revert
  | _, _, .assumeFalse, _, _ => CKeeps.halt .exhausted
  | Γ, _, .call _ args ret body, outer, h => by
    have h' : Prog.ctSafe body (outer || Γ.hasAlias) = true := h
    exact CKeeps.call args ret body.ext
      ((Prog.keeps_ct body _ h').weaken fun hg => by rw [hg, Bool.true_or])
      fun ha => by rw [ha, Bool.or_true]
  | _, _, .callRec .., _, h => nomatch h
  | Γ, _, .callReceiver _ args r body op, outer, h => by
    have h' : (Prog.ctSafe body (outer || Γ.hasAlias) &&
        (op.isPush || _ || !(outer || Γ.hasAlias))) = true := h
    rw [Bool.and_eq_true] at h'
    refine ckeeps_callReceiver args r body.ext op
      ((Prog.keeps_ct body _ h'.1).weaken fun hg => by rw [hg, Bool.true_or])
      (fun ha => by rw [ha, Bool.or_true]) ?_
    have h2 := h'.2
    revert h2
    cases op.isPush <;> cases outer <;> cases Γ.hasAlias <;> simp
  | Γ, _, .callReceiverPush _ args r body code value, outer, h => by
    have h' : (Prog.ctSafe body (outer || Γ.hasAlias) && Prog.ctSafe code true) = true := h
    rw [Bool.and_eq_true] at h'
    exact ckeeps_callReceiverPush args r body.ext code.ext value
      ((Prog.keeps_ct body _ h'.1).weaken fun hg => by rw [hg, Bool.true_or])
      ((Prog.keeps_ct code true h'.2).weaken fun _ => rfl)
      (fun ha => by rw [ha, Bool.or_true])
  | Γ, _, .tryCall call rets ok err code pnc other sargs sbody self, outer, h => by
    have h' : (Prog.ctSafe ok outer && Prog.ctSafe err outer && Prog.ctSafe pnc outer &&
        Prog.ctSafe other outer && Prog.ctSafe sbody (outer || Γ.hasAlias)) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨⟨⟨hok, herr⟩, hpnc⟩, hoth⟩, hsb⟩ := h'
    refine CKeeps.tryCall call rets ok.ext err.ext code pnc.ext other.ext sargs sbody.ext self
      ((Prog.keeps_ct ok outer hok).weaken fun hg => ?_) (Prog.keeps_ct err outer herr)
      ((Prog.keeps_ct pnc outer hpnc).weaken fun hg => ?_) (Prog.keeps_ct other outer hoth)
      ((Prog.keeps_ct sbody _ hsb).weaken fun hg => by rw [hg, Bool.true_or])
      (fun ha => by rw [ha, Bool.or_true])
    · rcases Bool.or_eq_true_iff.mp hg with hg | hg
      · rw [hg, Bool.true_or]
      · rw [Ctx.hasAlias_append _ hg, Bool.or_true]
    · rcases Bool.or_eq_true_iff.mp hg with hg | hg
      · rw [hg, Bool.true_or]
      · rw [Ctx.hasAlias_append _ hg, Bool.or_true]
  | _, _, .loop _ c body, outer, h => CKeeps.loop c body.ext (Prog.keeps_ct body outer h)
  | _, _, .block body, outer, h => CKeeps.block body.ext (Prog.keeps_ct body outer h)
  | _, _, .revertData d, _, _ => ckeeps_revertData d
  | _, _, .catchData c rets sargs sbody self kind _ body, outer, h =>
    ckeeps_catchData c rets sargs sbody.ext sbody.runR self kind body.ext
      (Prog.keeps_ct body outer h)

/-- **A block that exposes nothing keeps clean tails.** -/
theorem Prog.keeps_ct : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → (outer : Bool) →
    P.ctSafe outer = true → CKeeps (outer || Γ.hasAlias) (Prog.runR P)
  | _, _, .nil, _, _ => CKeeps.nil
  | Γ, _, .cons s P, outer, h => by
    have h' : (Stmt.ctSafe s outer && Prog.ctSafe P outer) = true := h
    rw [Bool.and_eq_true] at h'
    exact CKeeps.seq (Stmt.keeps_ct s outer h'.1)
      ((Prog.keeps_ct P outer h'.2).weaken fun hg => by
        rcases Bool.or_eq_true_iff.mp hg with hg | hg
        · rw [hg, Bool.true_or]
        · rw [Ext.hasAlias s.ext hg, Bool.or_true])

end

/-! ## A contract that exposes nothing keeps clean tails -/

/-- **A run that exposes nothing keeps clean tails**: from a state with
clean tails and no alias local (a transaction's parameters are values and
memory), a program that passes the check ends with clean tails. -/
theorem Prog.run_cleanTail {Γ Γ' : Ctx} (P : Prog C Γ Γ') (hP : P.exposesNone = true)
    {σ : State C Γ} (hσ : σ.storage.CleanTail) (hΓ : Γ.hasAlias = false) {o : Out C σ.H Γ'}
    (h : P.run σ = .ok o) : o.st.storage.CleanTail :=
  (Prog.keeps_ct P false hP σ o ⟨hσ, env_noAlias _ hΓ _⟩ h).1.1

/-- **The storages a contract reaches through `F`**: the deployment's, and
whatever a run of a program `F` admits leaves, from a state over a reached
storage with no alias local (the constructor, then any sequence of
transactions). -/
inductive ReachableBy (C : Contract) (F : (Γ Γ' : Ctx) → Prog C Γ Γ' → Prop) :
    Storage C → Prop
  | init : ReachableBy C F (Storage.init C)
  | step {Γ Γ' : Ctx} (P : Prog C Γ Γ') (hP : F Γ Γ' P) (σ : State C Γ) (hΓ : Γ.hasAlias = false)
      (hσ : ReachableBy C F σ.storage) (o : Out C σ.H Γ') (h : P.run σ = .ok o) :
      ReachableBy C F o.st.storage

/-- **Clean tails are a contract's invariant** when every program it runs
exposes nothing: every storage it reaches has clean tails. -/
theorem ReachableBy.cleanTail {F : (Γ Γ' : Ctx) → Prog C Γ Γ' → Prop}
    (hF : ∀ {Γ Γ' : Ctx} (P : Prog C Γ Γ'), F Γ Γ' P → P.exposesNone = true) {st : Storage C}
    (h : ReachableBy C F st) : st.CleanTail := by
  induction h with
  | init => exact Storage.init_cleanTail C
  | step P hP σ hΓ _ o hr ih => exact P.run_cleanTail (hF P hP) ih hΓ hr

end Solidity
