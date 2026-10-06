import Solidity.Calculus.DecideLang

/-!
# The slots past an array's end, read live

`sol_decide` reads the live storage (`SVal.findLive`, `SVal.saveLive`,
`Calculus/DecideLang.lean`): every index on a path the program takes was
checked against the live length.  An alias bound through an index is the
exception (`Token storage r = tokens[0]; tokens.pop(); r.value = 5;`): KeY's
`at(i)` names a slot, not a live element, so the write through it is the
interpreter's slot-level `SVal.save`, and it lands in the slots past the end
(`SVal.array`'s `shadow`).  A later `push()`, `delete` or copy makes that
slot live again, and the live reader then sees what the stale write left.

This module is what those writes and readers amount to on one `SVal`,
apart from the language: a slot-level write read live (at its path, apart
from it, below and above it), the first slot past an array's end (the one a
`push()` recycles, `pushSlot`), and what a `delete`, a copy and a push leave
there.  Each fact is the interpreter's side of one of solkey's storage
taclets; the row of `docs/lean-key-rule-map.md` that names the taclet cites
the lemma of `Theory/` it transcribes.
-/

namespace Solidity

namespace Decide

open Semantics SemanticsProperties

/-! ## Two list facts

A slot-level write into an array rewrites `elems ++ shadow` and splits it
back at the live length. -/

private theorem take_set_length (elems shadow : List SVal) (k : Nat) (x : SVal) :
    (((elems ++ shadow).set k x).take elems.length).length = elems.length := by
  simp only [List.length_take, List.length_set, List.length_append]
  omega

private theorem take_set_getElem (elems shadow : List SVal) (k j : Nat) (x : SVal)
    (hj : j < (((elems ++ shadow).set k x).take elems.length).length) :
    (((elems ++ shadow).set k x).take elems.length)[j] =
      if k = j then x else elems[j]'(by rw [take_set_length] at hj; exact hj) := by
  have hj' : j < elems.length := by rw [take_set_length] at hj; exact hj
  simp only [List.getElem_take, List.getElem_set]
  split
  · rfl
  · exact List.getElem_append_left hj'

/-! ## A write at a slot, read live -/

/-- **A slot write, read at a prefix**: after the write at `ps ++ r`, the
live read at `ps` is the old value there with `r` written into it, and halts
where the old one did.  The index of an alias names a slot, so the write
may land past an array's end; the live read at `ps` checks every index of
`ps`, and the write keeps every length. -/
theorem findLive_save_prefix {new : SVal} : ∀ {v u : SVal} {ps : List Seg} (r : List Seg),
    v.save (ps ++ r) new = .ok u → u.findLive ps = (v.findLive ps >>= fun c => c.save r new)
  | v, u, [], r, h => by
    simp only [List.nil_append] at h
    simp only [SVal.findLive_nil, Res.ok_bind, h]
  | .prim _, _, a :: _, _, h => by
    cases a <;> simp only [List.cons_append, SVal.save, reduceCtorEq] at h
  | .struct fields, u, .field n :: ps, r, h => by
    simp only [List.cons_append, SVal.save] at h
    split at h
    · rename_i old hl
      obtain ⟨upd, hu, h⟩ := Res.bind_eq_ok.1 h
      cases h
      simp only [SVal.findLive, lookupBy_setBy_self, hl, findLive_save_prefix r hu]
    · simp only [reduceCtorEq] at h
  | .struct _, _, .at _ :: _, _, h => by
    simp only [List.cons_append, SVal.save, reduceCtorEq] at h
  | .array elems shadow fx, u, .at i :: ps, r, h => by
    simp only [List.cons_append, SVal.save] at h
    split at h
    · rename_i hi
      obtain ⟨upd, hu, h⟩ := Res.bind_eq_ok.1 h
      cases h
      simp only [List.get_eq_getElem] at hu
      by_cases hl : 0 ≤ i ∧ i.toNat < elems.length
      · have hl' : 0 ≤ i ∧ i.toNat <
            (((elems ++ shadow).set i.toNat upd).take elems.length).length := by
          rw [take_set_length]; exact hl
        rw [List.getElem_append_left hl.2] at hu
        simp only [SVal.findLive, dif_pos hl, dif_pos hl', List.get_eq_getElem,
          take_set_getElem, if_true, findLive_save_prefix r hu]
      · have hl' : ¬ (0 ≤ i ∧ i.toNat <
            (((elems ++ shadow).set i.toNat upd).take elems.length).length) := by
          rw [take_set_length]; exact hl
        simp only [SVal.findLive, dif_neg hl, dif_neg hl']
        rfl
    · simp only [reduceCtorEq] at h
  | .array _ _ _, _, .field _ :: _, _, h => by
    simp only [List.cons_append, SVal.save, reduceCtorEq] at h
  | .map entries dflt, u, .at i :: ps, r, h => by
    simp only [List.cons_append, SVal.save] at h
    split at h
    · rename_i old hl
      obtain ⟨upd, hu, h⟩ := Res.bind_eq_ok.1 h
      cases h
      simp only [SVal.findLive, lookupBy_setBy_self, hl, findLive_save_prefix r hu]
    · rename_i hl
      obtain ⟨upd, hu, h⟩ := Res.bind_eq_ok.1 h
      cases h
      simp only [SVal.findLive, lookupBy_setBy_self, hl, findLive_save_prefix r hu]
  | .map _ _, _, .field _ :: _, _, h => by
    simp only [List.cons_append, SVal.save, reduceCtorEq] at h

/-- **Read at a slot write** (`selectOnSaveCons`, `a1 = a2`): the written
value where the old path was live, a halt where it was not, since a slot
write keeps every length. -/
theorem findLive_save_live {new v u : SVal} {ps : List Seg} (h : v.save ps new = .ok u) :
    u.findLive ps = (v.findLive ps >>= fun _ => .ok new) := by
  rw [← List.append_nil ps] at h
  rw [findLive_save_prefix [] h]
  congr 1
  funext c
  exact SVal.save_nil c new

/-- **Frame of a slot write** (`selectOnSaveCons`, `a1 ≠ a2`): the live read
apart from the written slot is as it was. -/
theorem findLive_save_diverge {new : SVal} :
    ∀ {p q : List Seg} {old upd : SVal}, Close.Diverge p q → old.save p new = .ok upd →
      upd.findLive q = old.findLive q
  | [], _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => (Close.not_diverge_nil_right h).elim
  | a :: p, b :: q, old, upd, h, hs => by
    cases old with
    | prim v => cases a <;> simp only [SVal.save, reduceCtorEq] at hs
    | struct fields =>
      cases a with
      | «at» i => simp only [SVal.save, reduceCtorEq] at hs
      | field n =>
        simp only [SVal.save] at hs
        split at hs
        · rename_i old' hl
          obtain ⟨u, hu, hs⟩ := Res.bind_eq_ok.1 hs
          cases hs
          cases b with
          | «at» j => simp only [SVal.findLive]
          | field m =>
            by_cases hnm : m = n
            · subst hnm
              have hd : Close.Diverge p q := by simpa only [Close.diverge_cons, ne_eq,
                  not_true_eq_false, false_or] using h
              simp only [SVal.findLive, lookupBy_setBy_self, findLive_save_diverge hd hu, hl]
            · simp only [SVal.findLive, lookupBy_setBy_ne hnm]
        · simp only [reduceCtorEq] at hs
    | array elems shadow fx =>
      cases a with
      | field n => simp only [SVal.save, reduceCtorEq] at hs
      | «at» i =>
        simp only [SVal.save] at hs
        split at hs
        · rename_i hi
          obtain ⟨u, hu, hs⟩ := Res.bind_eq_ok.1 hs
          simp only [List.get_eq_getElem] at hu
          cases hs
          cases b with
          | field m =>
            -- `length` reads the live extent, which a slot write keeps
            by_cases hm : m = "length"
            · subst hm
              cases fx <;> simp only [SVal.findLive, Bool.false_eq_true, ↓reduceIte,
                take_set_length]
            · simp only [SVal.findLive]
          | «at» j =>
            by_cases hj : 0 ≤ j ∧ j.toNat < elems.length
            · have hj' : 0 ≤ j ∧ j.toNat <
                  (((elems ++ shadow).set i.toNat u).take elems.length).length := by
                rw [take_set_length]; exact hj
              simp only [SVal.findLive, dif_pos hj, dif_pos hj', List.get_eq_getElem,
                take_set_getElem]
              by_cases hij : i.toNat = j.toNat
              · have hij' : j = i := by omega
                subst hij'
                have hd : Close.Diverge p q := by simpa only [Close.diverge_cons, ne_eq,
                    not_true_eq_false, false_or] using h
                rw [List.getElem_append_left hj.2] at hu
                simp only [if_true, findLive_save_diverge hd hu]
              · simp only [hij, if_false]
            · have hj' : ¬ (0 ≤ j ∧ j.toNat <
                  (((elems ++ shadow).set i.toNat u).take elems.length).length) := by
                rw [take_set_length]; exact hj
              simp only [SVal.findLive, dif_neg hj, dif_neg hj']
        · simp only [reduceCtorEq] at hs
    | map entries dflt =>
      cases a with
      | field n => simp only [SVal.save, reduceCtorEq] at hs
      | «at» i =>
        simp only [SVal.save] at hs
        -- the slot written: the entry at `i`, or the default when there is none
        obtain ⟨old', hold, hfind⟩ : ∃ old' : SVal, (old'.save p new >>= fun u =>
            Except.ok (SVal.map (setBy i u entries) dflt)) = Except.ok upd ∧
            (SVal.map entries dflt).findLive (.at i :: q) = old'.findLive q := by
          split at hs <;> rename_i hl <;> exact ⟨_, hs, by simp only [SVal.findLive, hl]⟩
        obtain ⟨u, hu, hold⟩ := Res.bind_eq_ok.1 hold
        cases hold
        cases b with
        | field m => simp only [SVal.findLive]
        | «at» j =>
          by_cases hij : j = i
          · subst hij
            have hd : Close.Diverge p q := by simpa only [Close.diverge_cons, ne_eq,
                not_true_eq_false, false_or] using h
            simp only [SVal.findLive, lookupBy_setBy_self] at hfind ⊢
            rw [hfind, findLive_save_diverge hd hu]
          · simp only [SVal.findLive, lookupBy_setBy_ne hij]

/-- A write below a value keeps its shape: a struct stays a struct, an
array an array of the same length and kind, a mapping a mapping. -/
theorem save_cons_shape {a : Seg} {r : List Seg} {new c c' : SVal}
    (h : c.save (a :: r) new = .ok c') :
    Close.arrLen c' = Close.arrLen c ∧ isMapV c' = isMapV c ∧ isFixV c' = isFixV c := by
  cases c with
  | prim _ => cases a <;> simp only [SVal.save, reduceCtorEq] at h
  | struct fields =>
    cases a with
    | «at» _ => simp only [SVal.save, reduceCtorEq] at h
    | field n =>
      simp only [SVal.save] at h
      split at h
      · obtain ⟨_, _, h⟩ := Res.bind_eq_ok.1 h
        cases h
        exact ⟨rfl, rfl, rfl⟩
      · simp only [reduceCtorEq] at h
  | array elems shadow fx =>
    cases a with
    | field _ => simp only [SVal.save, reduceCtorEq] at h
    | «at» i =>
      simp only [SVal.save] at h
      split at h
      · obtain ⟨_, _, h⟩ := Res.bind_eq_ok.1 h
        cases h
        simp only [Close.arrLen, take_set_length, isMapV, isFixV, and_self]
      · simp only [reduceCtorEq] at h
  | map entries dflt =>
    cases a with
    | field _ => simp only [SVal.save, reduceCtorEq] at h
    | «at» i =>
      simp only [SVal.save] at h
      split at h <;>
        (obtain ⟨_, _, h⟩ := Res.bind_eq_ok.1 h; cases h; exact ⟨rfl, rfl, rfl⟩)

/-- **Read below a slot write of a word**: it halts, as a read below any
word does. -/
theorem findLive_save_below {x : PrimVal} {v u : SVal} {ps : List Seg} (a : Seg)
    (r : List Seg) (h : v.save ps (.prim x) = .ok u) (y : SVal) :
    u.findLive (ps ++ a :: r) ≠ .ok y := by
  rw [SVal.findLive_append, findLive_save_live h]
  cases v.findLive ps with
  | error _ => simp only [Res.error_bind, ne_eq, reduceCtorEq, not_false_eq_true]
  | ok _ => cases a <;> simp only [Res.ok_bind, SVal.findLive, ne_eq, reduceCtorEq,
      not_false_eq_true]

/-- A write below a value leaves no word there. -/
theorem save_cons_noWord {a : Seg} {r : List Seg} {new c c' : SVal}
    (h : c.save (a :: r) new = .ok c') (y : Value) : c'.asValue ≠ .ok y := by
  have hw : ∀ c' : SVal, (match c' with | .prim _ => False | _ => True) →
      c'.asValue ≠ .ok y := fun c' hc => by
    cases c' with
    | prim _ => exact hc.elim
    | struct _ | array _ _ _ | map _ _ => simp only [SVal.asValue, ne_eq, reduceCtorEq,
        not_false_eq_true]
  apply hw
  cases c with
  | prim _ => cases a <;> simp only [SVal.save, reduceCtorEq] at h
  | struct fields =>
    cases a with
    | «at» _ => simp only [SVal.save, reduceCtorEq] at h
    | field n =>
      simp only [SVal.save] at h
      split at h
      · obtain ⟨_, _, h⟩ := Res.bind_eq_ok.1 h
        cases h
        trivial
      · simp only [reduceCtorEq] at h
  | array elems shadow fx =>
    cases a with
    | field _ => simp only [SVal.save, reduceCtorEq] at h
    | «at» i =>
      simp only [SVal.save] at h
      split at h
      · obtain ⟨_, _, h⟩ := Res.bind_eq_ok.1 h
        cases h
        trivial
      · simp only [reduceCtorEq] at h
  | map entries dflt =>
    cases a with
    | field _ => simp only [SVal.save, reduceCtorEq] at h
    | «at» i =>
      simp only [SVal.save] at h
      split at h <;> (obtain ⟨_, _, h⟩ := Res.bind_eq_ok.1 h; cases h; trivial)

/-- **Read above a slot write**: the live read there returns no word, since
the write went through it. -/
theorem findLive_save_above {new v u : SVal} {ps : List Seg} (a : Seg) (r : List Seg)
    (h : v.save (ps ++ a :: r) new = .ok u) (y : Value) :
    (u.findLive ps >>= SVal.asValue) ≠ .ok y := by
  rw [findLive_save_prefix (a :: r) h]
  cases v.findLive ps with
  | error _ => simp only [Res.error_bind, ne_eq, reduceCtorEq, not_false_eq_true]
  | ok c =>
    rw [Res.ok_bind]
    cases hc : c.save (a :: r) new with
    | error _ => simp only [Res.error_bind, ne_eq, reduceCtorEq, not_false_eq_true]
    | ok c' => rw [Res.ok_bind]; exact save_cons_noWord hc y

/-! ## The first slot past the end

The slot `ps ++ [at(n)]` of the array of `n` elements at `ps`: the head of
its `shadow`, the slot a `push()` of a struct or an array recycles as it is
(`pushSlot`, `storagePushLengthSaveReferenceElement`). -/

/-- The slot past the end reads the head of the slots past the end. -/
theorem find_shadow_head (es : List SVal) (c : SVal) (sh : List SVal) (fx : Bool)
    (r : List Seg) : (SVal.array es (c :: sh) fx).find (.at es.length :: r) = c.find r := by
  simp only [SVal.find, Int.ofNat_zero_le, Int.toNat_natCast, List.length_append,
    List.length_cons, true_and, Nat.lt_add_of_pos_right (Nat.succ_pos _), ↓reduceDIte,
    List.get_eq_getElem, Nat.le_refl, List.getElem_append_right, Nat.sub_self,
    List.getElem_cons_zero]

/-- An array with no slot past its end has none to read there. -/
theorem find_shadow_nil (es : List SVal) (fx : Bool) (r : List Seg) :
    (SVal.array es [] fx).find (.at es.length :: r) = .error .revert := by
  simp only [SVal.find, Int.ofNat_zero_le, Int.toNat_natCast, List.append_nil,
    Nat.lt_irrefl, and_false, ↓reduceDIte]

/-- A write at the slot past the end writes the head of the slots past the
end, and leaves the live elements and the length as they were. -/
theorem save_shadow_head (es : List SVal) (c : SVal) (sh : List SVal) (fx : Bool)
    (r : List Seg) (new : SVal) :
    (SVal.array es (c :: sh) fx).save (.at es.length :: r) new =
      (c.save r new >>= fun c' => .ok (.array es (c' :: sh) fx)) := by
  simp only [SVal.save, Int.ofNat_zero_le, Int.toNat_natCast, List.length_append,
    List.length_cons, true_and, Nat.lt_add_of_pos_right (Nat.succ_pos _), ↓reduceDIte,
    List.get_eq_getElem, Nat.le_refl, List.getElem_append_right, Nat.sub_self,
    List.getElem_cons_zero, List.set_append_right, List.set_cons_zero,
    List.take_left', List.drop_left']

/-- An array with no slot past its end has none to write there. -/
theorem save_shadow_nil (es : List SVal) (fx : Bool) (r : List Seg) (new : SVal) :
    (SVal.array es [] fx).save (.at es.length :: r) new = .error .revert := by
  simp only [SVal.save, Int.ofNat_zero_le, Int.toNat_natCast, List.append_nil,
    Nat.lt_irrefl, and_false, ↓reduceDIte]

/-- The slot past the end of a live array, read at the slot level. -/
theorem find_past_end {v : SVal} {ps : List Seg} {es : List SVal} {c : SVal} {sh : List SVal}
    {fx : Bool} (h : v.findLive ps = .ok (.array es (c :: sh) fx)) (r : List Seg) :
    v.find (ps ++ .at es.length :: r) = c.find r := by
  rw [SVal.find_append, SVal.find_of_findLive h, Res.ok_bind, find_shadow_head]

/-- A live array with no slot past its end: the slot-level read there halts. -/
theorem find_past_end_nil {v : SVal} {ps : List Seg} {es : List SVal} {fx : Bool}
    (h : v.findLive ps = .ok (.array es [] fx)) (r : List Seg) :
    v.find (ps ++ .at es.length :: r) = .error .revert := by
  rw [SVal.find_append, SVal.find_of_findLive h, Res.ok_bind, find_shadow_nil]

/-- **A write through a dangling alias** (`storageFieldWriteSave` with `sp` an
alias bound to `a[n-1]` before a `pop`): the array is as long as it was, and
the slot the next `push()` recycles holds the write. -/
theorem findLive_save_past_end {new v u : SVal} {ps r : List Seg} {es : List SVal} {c : SVal}
    {sh : List SVal} {fx : Bool} (h : v.findLive ps = .ok (.array es (c :: sh) fx))
    (hs : v.save (ps ++ .at es.length :: r) new = .ok u) :
    ∃ c', c.save r new = .ok c' ∧ u.findLive ps = .ok (.array es (c' :: sh) fx) := by
  have hu := findLive_save_prefix (.at es.length :: r) hs
  rw [h, Res.ok_bind, save_shadow_head] at hu
  have hf : v.find ps = .ok (.array es (c :: sh) fx) := SVal.find_of_findLive h
  rw [SVal.save_append v ps _ new _ hf, save_shadow_head] at hs
  obtain ⟨x, hx, -⟩ := Res.bind_eq_ok.1 hs
  obtain ⟨c', hc', -⟩ := Res.bind_eq_ok.1 hx
  exact ⟨c', hc', by rw [hu, hc', Res.ok_bind]⟩

/-! ## What a `delete`, a copy and a push leave past the end -/

/-- **`delete` of an empty dynamic array** (`delAtEmpty`, then
`selectStDelNodeIndexStruct` at `iv ≥ size`): the slots past its end are
kept as they were. -/
theorem defaultOf_array_nil (sh : List SVal) :
    (SVal.array [] sh false).defaultOf = .array [] sh false := by
  simp only [SVal.defaultOf, SVal.defaultOf.defaultOfElems, List.nil_append]

/-- **A deleted value has the slots it had** (`delFieldIndexStruct`,
`selectStDelNodeDefault`): `delete` empties a dynamic array into its slots
past the end and resets the rest in place, so a slot-level read returns
exactly where it did. -/
theorem defaultOf_find_ok : ∀ (v : SVal) (p : List Seg),
    (∃ x, v.defaultOf.find p = .ok x) ↔ ∃ x, v.find p = .ok x
  | v, [] => by
    simp only [SVal.find_nil]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  | .prim (.int _), a :: _ => by cases a <;> simp only [SVal.defaultOf, SVal.find, reduceCtorEq,
      exists_false]
  | .prim (.bool _), a :: _ => by cases a <;> simp only [SVal.defaultOf, SVal.find, reduceCtorEq,
      exists_false]
  | .struct fields, .field n :: p => by
    simp only [SVal.defaultOf, SVal.find, lookupBy_defaultOfFields]
    cases lookupBy n fields with
    | none => simp only [Option.map_none, reduceCtorEq, exists_false]
    | some w => simp only [Option.map_some, defaultOf_find_ok w p]
  | .struct _, .at _ :: _ => by simp only [SVal.defaultOf, SVal.find, reduceCtorEq, exists_false]
  | .array elems shadow false, .at i :: p => by
    simp only [SVal.defaultOf, SVal.find, List.nil_append, defaultOfElems_eq_map]
    by_cases hi : 0 ≤ i ∧ i.toNat < (elems ++ shadow).length
    · have hi' : 0 ≤ i ∧ i.toNat < (elems.map SVal.defaultOf ++ shadow).length := by
        simp only [List.length_append, List.length_map] at hi ⊢; exact hi
      rw [dif_pos hi, dif_pos hi']
      simp only [List.get_eq_getElem, List.getElem_append]
      by_cases he : i.toNat < elems.length
      · have he' : i.toNat < (elems.map SVal.defaultOf).length := by
          rw [List.length_map]; exact he
        rw [dif_pos he, dif_pos he', List.getElem_map]
        exact defaultOf_find_ok _ p
      · simp only [dif_neg he, List.length_map]
    · have hi' : ¬ (0 ≤ i ∧ i.toNat < (elems.map SVal.defaultOf ++ shadow).length) := by
        simp only [List.length_append, List.length_map] at hi ⊢; exact hi
      rw [dif_neg hi, dif_neg hi']
  | .array elems shadow true, .at i :: p => by
    simp only [SVal.defaultOf, SVal.find, defaultOfElems_eq_map]
    by_cases hi : 0 ≤ i ∧ i.toNat < (elems ++ shadow).length
    · have hi' : 0 ≤ i ∧ i.toNat < (elems.map SVal.defaultOf ++ shadow).length := by
        simp only [List.length_append, List.length_map] at hi ⊢; exact hi
      rw [dif_pos hi, dif_pos hi']
      simp only [List.get_eq_getElem, List.getElem_append]
      by_cases he : i.toNat < elems.length
      · have he' : i.toNat < (elems.map SVal.defaultOf).length := by
          rw [List.length_map]; exact he
        rw [dif_pos he, dif_pos he', List.getElem_map]
        exact defaultOf_find_ok _ p
      · simp only [dif_neg he, List.length_map]
    · have hi' : ¬ (0 ≤ i ∧ i.toNat < (elems.map SVal.defaultOf ++ shadow).length) := by
        simp only [List.length_append, List.length_map] at hi ⊢; exact hi
      rw [dif_neg hi, dif_neg hi']
  | .array elems shadow fx, .field n :: p => by
    by_cases hn : n = "length"
    · subst hn
      cases fx
      · cases p with
        | nil =>
          simp only [SVal.defaultOf, SVal.find, Bool.false_eq_true, ↓reduceIte]
          exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
        | cons a _ => cases a <;> simp only [SVal.defaultOf, SVal.find, Bool.false_eq_true,
            ↓reduceIte, reduceCtorEq, exists_false]
      · simp only [SVal.defaultOf, SVal.find, ↓reduceIte, reduceCtorEq, exists_false]
    · cases fx <;> simp only [SVal.defaultOf, SVal.find, reduceCtorEq, exists_false]
  | .map entries dflt, a :: p => by simp only [SVal.defaultOf]

/-- **The length of a deleted array** (`delFieldIndexStruct`,
`selectStDelNodeDefault` on `size`): `0` for a dynamic one, its own for a
fixed-size one. -/
theorem defaultOf_arrLen (es sh : List SVal) (fx : Bool) :
    Close.arrLen (SVal.array es sh fx).defaultOf = .ok (.int (if fx then es.length else 0)) := by
  cases fx <;> simp only [SVal.defaultOf, Close.arrLen, defaultOfElems_eq_map, List.length_map,
    List.length_nil, Bool.false_eq_true, ↓reduceIte, Int.natCast_zero]

private theorem stripElems_len : ∀ (vs : List SVal),
    (SVal.strip.stripElems vs).length = vs.length
  | [] => rfl
  | v :: vs => by simp only [SVal.strip.stripElems, List.length_cons, stripElems_len vs]

private theorem overlayElems_len : ∀ (os vs : List SVal),
    (SVal.overlay.overlayElems os vs).length = vs.length
  | [], [] => rfl
  | _ :: _, [] => rfl
  | [], v :: vs => by simp only [SVal.overlay.overlayElems, stripElems_len]
  | o :: os, v :: vs => by
    simp only [SVal.overlay.overlayElems, List.length_cons, overlayElems_len os vs]

/-- **A copy over a longer array** (`selectOnSaveEmptyIndexStruct`, its
second branch, `selectOnCopyIndexClear`): the first slot past the new end is
the old element there, deleted. -/
theorem overlay_shadow_lt {oel osh nel nsh : List SVal} {ofx nfx : Bool}
    (h : nel.length < oel.length) :
    ∃ el' sh', (SVal.array oel osh ofx).overlay (.array nel nsh nfx) =
      .array el' ((oel[nel.length]'h).defaultOf :: sh') nfx ∧ el'.length = nel.length := by
  refine ⟨SVal.overlay.overlayElems (oel ++ osh) nel,
    SVal.defaultOf.defaultOfElems (oel.drop (nel.length + 1)) ++
    osh.drop (nel.length - oel.length), ?_, overlayElems_len _ _⟩
  simp only [SVal.overlay, defaultOfElems_eq_map, List.drop_eq_getElem_cons h, List.map_cons,
    List.cons_append]

/-- **A copy over an array as long** (`selectOnSaveEmptyIndexStruct`, its
third branch, `selectOnCopyIndexKeep`): the slots past the end are the old
ones. -/
theorem overlay_shadow_eq {oel osh nel nsh : List SVal} {ofx nfx : Bool}
    (h : nel.length = oel.length) :
    ∃ el', (SVal.array oel osh ofx).overlay (.array nel nsh nfx) = .array el' osh nfx ∧
      el'.length = nel.length := by
  refine ⟨SVal.overlay.overlayElems (oel ++ osh) nel, ?_, overlayElems_len _ _⟩
  simp only [SVal.overlay, h, List.drop_length, defaultOfElems_eq_map, List.map_nil,
    Nat.sub_self, List.drop_zero, List.nil_append]

/-- **A push of a word** (`storagePushValueSave`): the array one longer, the
word at its old length. -/
theorem AOp.apply_push_eq {w : Value} {c c' : SVal} (h : AOp.push.apply w c = .ok c') :
    ∃ es sh fx, c = .array es sh fx ∧ c' = .array (es ++ [w.toSVal]) (pushSlot .uint sh).2 fx := by
  cases c with
  | array es sh fx =>
    simp only [AOp.apply, Except.ok.injEq] at h
    exact ⟨es, sh, fx, rfl, h.symm⟩
  | prim _ | struct _ | map _ _ => simp only [AOp.apply, reduceCtorEq] at h

/-- **A push of a word, read live** (`findDefinitionSize`, then
`selectOnSaveCons` on the `size` and the `at(n)` writes): the length is one
more, the slot at the old length is the word, the elements below it are as
they were. -/
theorem apply_push_find {w : Value} {c c' : SVal} (h : AOp.push.apply w c = .ok c') :
    ∃ n : Nat, Close.arrLen c = .ok (.int n) ∧ Close.arrLen c' = .ok (.int (n + 1)) ∧
      c'.findLive [.at n] = .ok w.toSVal ∧
      ∀ (j : Int) (r : List Seg), j ≠ n → c'.findLive (.at j :: r) = c.findLive (.at j :: r) := by
  obtain ⟨es, sh, fx, rfl, rfl⟩ := AOp.apply_push_eq h
  refine ⟨es.length, rfl, by simp only [Close.arrLen, List.length_append, List.length_cons,
    List.length_nil, Nat.zero_add, Int.natCast_add, Int.cast_ofNat_Int], ?_, ?_⟩
  · simp only [SVal.findLive, Int.ofNat_zero_le, Int.toNat_natCast, List.length_append,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, and_self, ↓reduceDIte,
      List.get_eq_getElem, Nat.le_refl, List.getElem_append_right, Nat.sub_self,
      List.getElem_cons_zero, SVal.findLive_nil]
  · intro j r hj
    by_cases hl : 0 ≤ j ∧ j.toNat < es.length
    · have hl' : 0 ≤ j ∧ j.toNat < (es ++ [w.toSVal]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      simp only [SVal.findLive, dif_pos hl, dif_pos hl', List.get_eq_getElem,
        List.getElem_append_left hl.2]
    · have hl' : ¬ (0 ≤ j ∧ j.toNat < (es ++ [w.toSVal]).length) := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      simp only [SVal.findLive, dif_neg hl, dif_neg hl']

/-- Below a pushed array an array is read only at an old element, as it
was: the pushed word has nothing below it, and the one member of an array
is its length. -/
theorem apply_push_findLive_array {w : Value} {c c' : SVal} (h : AOp.push.apply w c = .ok c')
    {f : Seg} {r : List Seg} {es sh : List SVal} {fx : Bool}
    (hn : c'.findLive (f :: r) = .ok (.array es sh fx)) :
    c.findLive (f :: r) = .ok (.array es sh fx) := by
  obtain ⟨n, -, -, hnew, hold⟩ := apply_push_find h
  cases f with
  | «at» j =>
    by_cases hj : j = n
    · subst hj
      exfalso
      rw [show (Seg.at (n : Int) :: r) = [Seg.at n] ++ r from rfl, SVal.findLive_append,
        hnew, Res.ok_bind] at hn
      cases w <;> cases r <;> simp only [Value.toSVal, SVal.findLive, Except.ok.injEq,
        reduceCtorEq] at hn
    · rw [← hold j r hj]; exact hn
  | field g =>
    exfalso
    obtain ⟨es0, sh0, fx0, -, rfl⟩ := AOp.apply_push_eq h
    by_cases hg : g = "length"
    · subst hg
      cases fx0 <;> cases r <;> simp only [SVal.findLive, Bool.false_eq_true, ↓reduceIte,
        Except.ok.injEq, reduceCtorEq] at hn
    · rw [SVal.findLive.eq_def] at hn
      split at hn <;> simp_all only [ne_eq, imp_false, SVal.array.injEq, List.cons.injEq,
        Seg.field.injEq, reduceCtorEq, false_and]

/-! ## A slot write against the slot past the end

What the elimination's `.stale` arms need: a slot-level write compared with
the first slot past an array's end, read at `r` below it. -/

/-- Two paths that part ways part ways either way round. -/
theorem diverge_flip : ∀ {p q : List Seg}, Close.Diverge p q → Close.Diverge q p
  | [], _, h => h.elim
  | _ :: _, [], h => (Close.not_diverge_nil_right h).elim
  | a :: p, b :: q, h => by
    rcases (Close.diverge_cons.1 h) with hab | hd
    · exact Close.diverge_cons.2 (.inl fun e => hab e.symm)
    · exact Close.diverge_cons.2 (.inr (diverge_flip hd))

/-- A path parting from `p ++ r` parts from `p`, or runs through `p` and
parts from `r` below it. -/
theorem diverge_append_split : ∀ {q p r : List Seg}, Close.Diverge q (p ++ r) →
    Close.Diverge q p ∨ ∃ t, q = p ++ t ∧ Close.Diverge t r
  | q, [], _, h => .inr ⟨q, rfl, h⟩
  | [], _ :: _, _, h => h.elim
  | b :: q, a :: p, r, h => by
    by_cases hab : b = a
    · subst hab
      rcases diverge_append_split (Close.diverge_cons.1 h |>.resolve_left (fun e => e rfl))
        with hd | ⟨t, rfl, ht⟩
      · exact .inl (Close.diverge_cons.2 (.inr hd))
      · exact .inr ⟨t, rfl, ht⟩
    · exact .inl (Close.diverge_cons.2 (.inl hab))

/-- A slot write succeeds only where the slot-level read of its path does. -/
theorem find_ok_of_save_ok {v new u : SVal} {ps : List Seg} (h : v.save ps new = .ok u) :
    ∃ c, v.find ps = .ok c := by
  cases hf : v.find ps with
  | ok c => exact ⟨c, rfl⟩
  | error e => rw [Close.save_of_find_error hf] at h; cases h

/-- A slot write succeeds where the slot-level read of its path does, on a
path with no `length` member (a write has no `length` arm). -/
theorem save_ok_of_find_ok {new : SVal} : ∀ {v c : SVal} {ps : List Seg},
    (∀ s ∈ ps, s ≠ .field "length") → v.find ps = .ok c → ∃ u, v.save ps new = .ok u
  | v, _, [], _, _ => ⟨new, SVal.save_nil v new⟩
  | v, c, s :: ps, hn, h => by
    have hn' : ∀ t ∈ ps, t ≠ .field "length" := fun t ht => hn t (.tail _ ht)
    have hs : s ≠ .field "length" := hn s (.head _)
    cases v with
    | prim p => cases s <;> simp only [SVal.find, reduceCtorEq] at h
    | struct fields =>
      cases s with
      | «at» _ => simp only [SVal.find, reduceCtorEq] at h
      | field n =>
        simp only [SVal.find] at h
        simp only [SVal.save]
        split at h
        · rename_i old hl
          obtain ⟨u, hu⟩ := save_ok_of_find_ok (new := new) hn' h
          exact ⟨_, by rw [hu]; rfl⟩
        · cases h
    | array elems shadow fx =>
      cases s with
      | field n =>
        have : n ≠ "length" := fun e => hs (by rw [e])
        simp only [SVal.find, reduceCtorEq] at h
      | «at» i =>
        simp only [SVal.find] at h
        simp only [SVal.save]
        split at h
        · rename_i hi
          obtain ⟨u, hu⟩ := save_ok_of_find_ok (new := new) hn' h
          exact ⟨_, by rw [dif_pos hi, hu]; rfl⟩
        · cases h
    | map entries dflt =>
      cases s with
      | field _ => simp only [SVal.find, reduceCtorEq] at h
      | «at» i =>
        simp only [SVal.find] at h
        simp only [SVal.save]
        split at h
        · rename_i old hl
          obtain ⟨u, hu⟩ := save_ok_of_find_ok (new := new) hn' h
          exact ⟨_, by rw [hu]; rfl⟩
        · rename_i hl
          obtain ⟨u, hu⟩ := save_ok_of_find_ok (new := new) hn' h
          exact ⟨_, by rw [hu]; rfl⟩

/-- A slot write through `p` writes the node at `p`: the slot-level read
there is the old node with the rest written. -/
theorem find_save_append {new v u : SVal} {p t : List Seg} (h : v.save (p ++ t) new = .ok u) :
    ∃ c c', v.find p = .ok c ∧ c.save t new = .ok c' ∧ u.find p = .ok c' := by
  obtain ⟨y, hy⟩ := find_ok_of_save_ok h
  rw [SVal.find_append] at hy
  obtain ⟨c, hc, -⟩ := Res.bind_eq_ok.1 hy
  rw [SVal.save_append v p t new c hc] at h
  obtain ⟨c', hc', hu⟩ := Res.bind_eq_ok.1 h
  exact ⟨c, c', hc, hc', SVal.find_save_same hu⟩

/-- A slot write against a slot it does not reach, read at `r` below the
node at `p`: either the node is as it was, or the write runs through `p` and
parts from `r` below it. -/
theorem find_save_diverge_tail {new v u : SVal} {qs p r : List Seg}
    (h : v.save qs new = .ok u) (hd : Close.Diverge qs (p ++ r)) :
    u.find p = v.find p ∨ ∃ t c c', qs = p ++ t ∧ Close.Diverge t r ∧ v.find p = .ok c ∧
      c.save t new = .ok c' ∧ u.find p = .ok c' := by
  rcases diverge_append_split hd with hd' | ⟨t, rfl, ht⟩
  · exact .inl (Close.find_save_diverge hd' h)
  · obtain ⟨c, c', hc, hc', hu⟩ := find_save_append h
    exact .inr ⟨t, c, c', rfl, ht, hc, hc', hu⟩

/-- A slot write below a live node: the node there is still live, the write
into it returns, and it is the new live node. -/
theorem save_prefix_ok {new v u c : SVal} {ps r : List Seg} (h : v.save (ps ++ r) new = .ok u)
    (hc : v.findLive ps = .ok c) : ∃ c', c.save r new = .ok c' ∧ u.findLive ps = .ok c' := by
  have hu := findLive_save_prefix r h
  rw [SVal.save_append v ps r new c (SVal.find_of_findLive hc)] at h
  obtain ⟨c', hc', -⟩ := Res.bind_eq_ok.1 h
  exact ⟨c', hc', by rw [hu, hc, Res.ok_bind, hc']⟩

/-- A slot write below a path keeps whether the live read there returns. -/
theorem findLive_save_prefix_has {new v u : SVal} {ps r : List Seg} (h : v.save (ps ++ r) new = .ok u) :
    (u.findLive ps >>= fun _ => .ok (Value.bool true)) =
      (v.findLive ps >>= fun _ => .ok (Value.bool true)) := by
  cases hc : v.findLive ps with
  | error e =>
    rw [findLive_save_prefix r h, hc]; rfl
  | ok c =>
    obtain ⟨c', -, hu⟩ := save_prefix_ok h hc
    rw [hu]; rfl

/-- A word written at or above a path leaves no array there. -/
theorem save_prim_not_array {x : PrimVal} {v u : SVal} {qs : List Seg} (z : List Seg)
    (h : v.save qs (.prim x) = .ok u) {es sh : List SVal} {fx : Bool} :
    u.findLive (qs ++ z) ≠ .ok (.array es sh fx) := by
  cases z with
  | nil =>
    rw [List.append_nil, findLive_save_live h]
    cases v.findLive qs <;> simp only [Res.error_bind, Res.ok_bind, ne_eq, reduceCtorEq,
      not_false_eq_true, Except.ok.injEq]
  | cons a r => exact findLive_save_below a r h _

/-- The slot past the end of a live array, as a result: its head, a halt
where it has none. -/
def headR : List SVal → Res SVal
  | c :: _ => .ok c
  | [] => .error .revert

/-- The slot-level read one past the live end reads the first slot past it. -/
theorem find_slot_head {v : SVal} {ps : List Seg} {es sh : List SVal} {fx : Bool}
    (h : v.findLive ps = .ok (.array es sh fx)) : v.find (ps ++ [.at es.length]) = headR sh := by
  cases sh with
  | nil => exact find_past_end_nil h []
  | cons c t => rw [find_past_end h [], SVal.find_nil]; rfl

end Decide

end Solidity
