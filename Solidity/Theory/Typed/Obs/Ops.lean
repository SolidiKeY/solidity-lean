import Solidity.Theory.Typed.Obs.Values

/-!
# Observations under the storage operations

Under a `select`, the operations on a storage, their bridge and laws.

A piece of `Theory/Typed/Obs.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy)

/-! ## Under a `select` -/

/-- A struct's members as the state variables of a contract: what
`select(s, r)` reads as a storage (`Storage (Contract.ofStruct s)`), and
where a path under it is rooted (`SRef (Contract.ofStruct s) T`), so the
storage's operations read it unchanged. -/
def Contract.ofStruct (s : Name) : Contract := { vars := structDef s }

/-- A path under `select(s, r)` as a path from the root `r`: its member
first. -/
def SRef.under {C : Contract} {s r : Name} {U : Ty} (q : SRef (Contract.ofStruct s) U)
    (h : C.rootType r = some (.ref (.struct s))) : SRef C U :=
  ⟨r, h, .field q.hroot q.path⟩

/-- The struct at the root `r` of `st`, as a storage of its members. -/
def Storage.selectT {C : Contract} {s r : Name} (st : Storage C)
    (h : C.rootType r = some (.ref (.struct s))) : Storage (Contract.ofStruct s) :=
  (SVal.view (st.get h) : SFields (structDef s))

/-- A location under `select(s, r)` as a location of the whole storage. -/
def SLoc.under {C : Contract} {s r : Name} {U : Ty} (h : C.rootType r = some (.ref (.struct s))) :
    SLoc (Contract.ofStruct s) U → SLoc C U
  | .ref q => .ref (q.under h)
  | .dangling V p => .dangling V p

/-- **`select(s, r)`**: the struct at the root `r`, read as a storage of its
members. -/
def Obs.select {C : Contract} {s r : Name} (o : TSto C) (h : C.rootType r = some (.ref (.struct s))) :
    TSto (Contract.ofStruct s) :=
  ⟨fun l => o.word (l.under h), fun l => o.len (l.under h), fun l => o.has (l.under h)⟩

theorem Storage.obs_selectT {C : Contract} {s r : Name} (st : Storage C)
    (h : C.rootType r = some (.ref (.struct s))) : (st.selectT h).obs = st.obs.select h := by
  have e : ∀ {U : Ty} (q : SRef (Contract.ofStruct s) U),
      (st.selectT h).get q.hroot = (SVal.view (st.get h) : SFields (structDef s)).get q.hroot := fun _ => rfl
  apply Obs.ext
  · intro P q
    cases q with
    | ref q =>
      show ((st.selectT h).get q.hroot).obs.word q.path = (st.get h).obs.word (.field q.hroot q.path)
      rw [e]; cases st.get h; rfl
    | dangling => rfl
  · intro E q
    cases q with
    | ref q =>
      show ((st.selectT h).get q.hroot).obs.len q.path = (st.get h).obs.len (.field q.hroot q.path)
      rw [e]; cases st.get h; rfl
    | dangling => rfl
  · intro V q
    cases q with
    | ref q =>
      show ((st.selectT h).get q.hroot).obs.has q.path = (st.get h).obs.has (.field q.hroot q.path)
      rw [e]; cases st.get h; rfl
    | dangling => rfl

/-! ## The operations on a storage

Each is a `save` at the location it acts on (`Obs.save`), of what the
location holds with the operation made on it: so its frame is `save`'s. -/

namespace Path

/-- The path that goes nowhere. -/
def isNilB {T U : Ty} : Path T U → Bool
  | .nil => true
  | _ => false

end Path

namespace TVal

/-- The array with its live length set. -/
def setLen {E : Ty} (a : TVal (.ref (.array E))) (k : Nat) : TVal (.ref (.array E)) :=
  ⟨a.word, fun r => if r.isNilB then k else a.len r, a.has⟩

/-- A word as a stored value. -/
def ofWord {P : PrimTy} (x : P.Denote) : TVal (.prim P) := (SVal.prim x).obs

/-- **`push`** onto an array: `x` appended past the live elements. -/
def pushA {E : Ty} (a : TVal (.ref (.array E))) (x : TVal E) : TVal (.ref (.array E)) :=
  TVal.setLen (a.save (.at (uintOfNat (a.len .nil)) .nil) x) (a.len .nil + 1)

/-- One more live element: the slot past the end as it is (a word reset, a
missing slot at its default). -/
def extendA {E : Ty} (a : TVal (.ref (.array E))) : TVal (.ref (.array E)) :=
  if E.isPrimitive || !a.has (.at (uintOfNat (a.len .nil)) .nil) then a.pushA (SVal.dflt E).obs
  else a.setLen (a.len .nil + 1)

/-- **`pop`**: the last live element moved past the end, reset unless
`keep`; an empty array as it is. -/
def popA {E : Ty} (keep : Bool) (a : TVal (.ref (.array E))) : TVal (.ref (.array E)) :=
  if a.len .nil = 0 then a
  else if keep then a.setLen (a.len .nil - 1)
  else TVal.setLen (a.save (.at (uintOfNat (a.len .nil - 1)) .nil)
    (TVal.del (a.find (.at (uintOfNat (a.len .nil - 1)) .nil)))) (a.len .nil - 1)

end TVal

namespace Obs

variable {L : Ty → Type} [ObsLoc L]

/-- **`delAt`**: the value at `p` deleted. -/
def delAt (o : Obs L) {U : Ty} (p : L U) : Obs L := o.save p (TVal.del (o.find p))
/-- **`save`** of a copy: `v` laid over what is at `p` (a word replaces). -/
def copyTo (o : Obs L) {U : Ty} (p : L U) (v : TVal U) : Obs L :=
  o.save p (TVal.overlay (o.find p) v)
/-- **`push`**: `x` appended to the array at `p`. -/
def push (o : Obs L) {E : Ty} (p : L (.ref (.array E))) (x : TVal E) : Obs L :=
  o.save p (TVal.pushA (o.find p) x)
/-- One more live element at the array at `p`, its slot as it is
(`pushSlot`, `extend`). -/
def extend (o : Obs L) {E : Ty} (p : L (.ref (.array E))) : Obs L :=
  o.save p (TVal.extendA (o.find p))
/-- **`pop`** at `p`, the element reset unless `keep` (`shrink`). -/
def pop (o : Obs L) (keep : Bool) {E : Ty} (p : L (.ref (.array E))) : Obs L :=
  o.save p (TVal.popA keep (o.find p))

end Obs

/-! ### The bridge of the storage operations -/

theorem TVal.overlay_prim {P : PrimTy} (o n : TVal (.prim P)) : o.overlay n = n := by
  apply Obs.ext
  · intro P' r; cases r; rfl
  · intro E r; cases r
  · intro V r; cases r; rfl

theorem List.getElem?_snoc_tail {β : Type} (l : List β) (x : β) (sh : List β) {k : Nat}
    (hk : k ≠ l.length) : (l ++ [x] ++ sh.tail)[k]? = (l ++ sh)[k]? := by
  rcases Nat.lt_or_gt_of_ne hk with hlt | hgt
  · rw [List.append_assoc, List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  · obtain ⟨m, rfl⟩ : ∃ m, k = l.length + 1 + m := ⟨k - l.length - 1, by omega⟩
    rw [List.append_assoc, List.singleton_append, List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega), show l.length + 1 + m - l.length = m + 1 by omega,
      List.getElem?_cons_succ]
    cases sh with
    | nil => rfl
    | cons c rest => rw [List.tail_cons, List.getElem?_cons_succ]

/-- An array with `x` appended, as the Theory's `pushA`. -/
theorem SVal.obs_pushArr {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (x : SVal E) (sh' : List (SVal E)) (hsh : sh' = sh.toList.tail)
    (h' : (e.toList ++ [x]).length < 2 ^ 256) :
    (SVal.array (SVec.ofList (e.toList ++ [x])) (SList.ofList sh') h').obs =
      TVal.pushA (SVal.array e sh hn).obs x.obs := by
  have hl : e.toList.length = n := SVec.length_toList e
  have hf : ∀ {W : Ty} (j : PrimTy.uint.Denote) (r : Path E W),
      (SVal.array (SVec.ofList (e.toList ++ [x])) (SList.ofList sh') h').findM (.at j r) =
        if uintOfNat n = j then x.findM r else (SVal.array e sh hn).findM (.at j r) := by
    intro W j r
    rw [SVal.findM_at', SVal.findM_at', SVec.toList_ofList, SList.toList_ofList, hsh]
    by_cases hj : uintOfNat n = j
    · subst hj
      simp only [if_true, uintOfNat_val hn, Int.natCast_nonneg, Int.toNat_natCast]
      rw [List.append_assoc, List.getElem?_append_right (by rw [hl]; exact Nat.le_refl _),
        hl, Nat.sub_self, List.singleton_append, List.getElem?_cons_zero, Option.bind_some]
    · have hj' : (n : Int) ≠ j.1 := fun e => hj (Subtype.ext ((uintOfNat_val hn).trans e))
      simp only [hj, if_false]
      have := PrimTy.uint_nonneg j
      rw [List.getElem?_snoc_tail _ _ _ (by rw [hl]; omega)]
  have el : (SVal.array e sh hn).obs.len .nil = n := rfl
  apply Obs.ext
  · intro P q
    cases q with
    | «at» j r =>
      show SVal.wordOf (_ : Option _) = _
      rw [Option.bind_some, hf]
      simp only [TVal.pushA, TVal.setLen, Obs.save, el, ObsLoc.strip?_path, Path.strip?]
      split <;> rfl
  · intro E' q
    cases q with
    | nil =>
      show (e.toList ++ [x]).length = _
      simp only [TVal.pushA, TVal.setLen, Path.isNilB, if_true, el, List.length_append, hl,
        List.length_singleton]
    | «at» j r =>
      show SVal.lenOf (_ : Option _) = _
      rw [Option.bind_some, hf]
      simp only [TVal.pushA, TVal.setLen, Path.isNilB, Bool.false_eq_true, if_false, Obs.save, el,
        ObsLoc.strip?_path, Path.strip?]
      split <;> rfl
  · intro V q
    cases q with
    | nil => rfl
    | «at» j r =>
      show Option.isSome _ = _
      rw [Option.bind_some, hf]
      simp only [TVal.pushA, TVal.setLen, Obs.save, el, ObsLoc.strip?_path, Path.strip?]
      split <;> rfl

/-- An array with the same slots and a new live length. -/
theorem SVal.obs_array_setLen {E : Ty} {n n' : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (e' : SVec E n') (sh' : SList E) (hn' : n' < 2 ^ 256)
    (hs : e'.toList ++ sh'.toList = e.toList ++ sh.toList) :
    (SVal.array e' sh' hn').obs = TVal.setLen (SVal.array e sh hn).obs n' := by
  have hf : ∀ {W : Ty} (j : PrimTy.uint.Denote) (r : Path E W),
      (SVal.array e' sh' hn').findM (.at j r) = (SVal.array e sh hn).findM (.at j r) := by
    intro W j r; rw [SVal.findM_at', SVal.findM_at', hs]
  apply Obs.ext
  · intro P q
    cases q with
    | «at» j r => show SVal.wordOf (_ : Option _) = SVal.wordOf (_ : Option _); rw [Option.bind_some,
        Option.bind_some, hf]
  · intro E' q
    cases q with
    | nil => rfl
    | «at» j r => show SVal.lenOf (_ : Option _) = SVal.lenOf (_ : Option _); rw [Option.bind_some,
        Option.bind_some, hf]
  · intro V q
    cases q with
    | nil => rfl
    | «at» j r => show Option.isSome _ = Option.isSome _; rw [Option.bind_some, Option.bind_some, hf]

/-- An array with one slot replaced and a new live length. -/
theorem SVal.obs_array_set {E : Ty} {n n' : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (e' : SVec E n') (sh' : SList E) (hn' : n' < 2 ^ 256) (k : Nat) (y : SVal E)
    (hk : k < (e.toList ++ sh.toList).length) (hkb : k < 2 ^ 256)
    (hs : e'.toList ++ sh'.toList = (e.toList ++ sh.toList).set k y) :
    (SVal.array e' sh' hn').obs =
      TVal.setLen ((SVal.array e sh hn).obs.save (.at (uintOfNat k) .nil) y.obs) n' := by
  have hf : ∀ {W : Ty} (j : PrimTy.uint.Denote) (r : Path E W),
      (SVal.array e' sh' hn').findM (.at j r) =
        if uintOfNat k = j then y.findM r else (SVal.array e sh hn).findM (.at j r) := by
    intro W j r
    rw [SVal.findM_at', SVal.findM_at', hs]
    by_cases hj : uintOfNat k = j
    · subst hj
      simp only [if_true, uintOfNat_val hkb, Int.natCast_nonneg, Int.toNat_natCast,
        List.getElem?_set_self hk, Option.bind_some]
    · have hj' : (k : Int) ≠ j.1 := fun e => hj (Subtype.ext ((uintOfNat_val hkb).trans e))
      simp only [hj, if_false]
      have := PrimTy.uint_nonneg j
      rw [List.getElem?_set_ne (by omega)]
  apply Obs.ext
  · intro P q
    cases q with
    | «at» j r =>
      show SVal.wordOf (_ : Option _) = _
      rw [Option.bind_some, hf]
      simp only [TVal.setLen, Obs.save, ObsLoc.strip?_path, Path.strip?]
      split <;> rfl
  · intro E' q
    cases q with
    | nil => rfl
    | «at» j r =>
      show SVal.lenOf (_ : Option _) = _
      rw [Option.bind_some, hf]
      simp only [TVal.setLen, Path.isNilB, Bool.false_eq_true, if_false, Obs.save,
        ObsLoc.strip?_path, Path.strip?]
      split <;> rfl
  · intro V q
    cases q with
    | nil => rfl
    | «at» j r =>
      show Option.isSome _ = _
      rw [Option.bind_some, hf]
      simp only [TVal.setLen, Obs.save, ObsLoc.strip?_path, Path.strip?]
      split <;> rfl

namespace Storage

variable {C : Contract}

theorem obs_find_some {U : Ty} {st : Storage C} {r : SRef C U} {w : SVal U} (h : st.find r = some w) :
    st.obs.find (.ref r) = w.obs := by
  rw [obs_find, h]; rfl

/-- **The bridge of a write**: a word saved, a value laid over what is there. -/
theorem obs_write {U : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    (h : st.write r v = some st') : st'.obs = st.obs.copyTo (.ref r) v.obs := by
  unfold Storage.write at h
  split at h
  · rename_i hp
    rw [obs_save h, Obs.copyTo]
    cases U with
    | prim P => rw [TVal.overlay_prim]
    | ref R => simp only [SVal.isPrim, Ty.isPrimitive, Bool.false_eq_true] at hp
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨cur, hc, h⟩ := h
    rw [obs_save h, Obs.copyTo, obs_find_some hc, SVal.obs_overlay]

/-- **The bridge of a delete.** -/
theorem obs_delete {U : Ty} {st st' : Storage C} {r : SRef C U} (h : st.delete r = some st') :
    st'.obs = st.obs.delAt (.ref r) := by
  unfold Storage.delete at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨cur, hc, h⟩ := h
  rw [obs_save h, Obs.delAt, obs_find_some hc, SVal.obs_defaultOf]


/-- A push that returns: the array found, its slot, the element made of it,
and the save of the array with it appended. -/
theorem push_some {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))}
    {val : SVal E → Option (SVal E)} (h : st.push r val = some st') :
    ∃ (n : Nat) (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256) (x : SVal E)
      (h' : (e.toList ++ [x]).length < 2 ^ 256),
      st.find r = some (.array e sh hn) ∧ val (pushSlot E sh.toList).1 = some x ∧
      st.save r (.array (SVec.ofList (e.toList ++ [x])) (.ofList (pushSlot E sh.toList).2) h') =
        some st' := by
  unfold Storage.push at h
  cases hf : st.find r with
  | none => simp only [hf, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some a =>
    cases a with
    | array e sh hn =>
      simp only [hf, Option.bind_eq_bind, Option.bind_some, SVal.view_array] at h
      cases hx : val (pushSlot _ sh.toList).1 with
      | none => simp only [hx, Option.bind_none, reduceCtorEq] at h
      | some x =>
        simp only [hx, Option.bind_some] at h
        split at h
        · exact ⟨_, e, sh, hn, x, _, rfl, hx, h⟩
        · cases h

theorem pushSlot_snd {E : Ty} (l : List (SVal E)) : (pushSlot E l).2 = l.tail := by
  cases l <;> rfl

/-- **The bridge of a push** of a value made of nothing of the slot. -/
theorem obs_push {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))} {x : SVal E}
    (h : st.push r (fun _ => some x) = some st') : st'.obs = st.obs.push (.ref r) x.obs := by
  obtain ⟨n, e, sh, hn, x', h', hf, hx, hs⟩ := push_some h
  cases hx
  rw [obs_save hs, Obs.push, obs_find_some hf,
    SVal.obs_pushArr e sh hn x _ (pushSlot_snd _) h']

/-- The slot past the end, appended as it is. -/
theorem obs_extendArr {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
    (h' : (e.toList ++ [(pushSlot E sh.toList).1]).length < 2 ^ 256) :
    (SVal.array (SVec.ofList (e.toList ++ [(pushSlot E sh.toList).1]))
      (.ofList (pushSlot E sh.toList).2) h').obs = TVal.extendA (SVal.array e sh hn).obs := by
  rw [SVal.obs_pushArr e sh hn _ _ (pushSlot_snd _) h', TVal.extendA]
  have hl : e.toList.length = n := SVec.length_toList e
  have el : (SVal.array e sh hn).obs.len .nil = n := rfl
  cases hs : sh.toList with
  | nil =>
    have hh : (SVal.array e sh hn).obs.has (.at (uintOfNat n) .nil) = false := by
      show Option.isSome ((some _).bind _) = false
      rw [Option.bind_some, SVal.findM_at', hs, List.append_nil]
      simp only [uintOfNat_val hn, Int.natCast_nonneg, if_true, Int.toNat_natCast]
      rw [List.getElem?_eq_none (by omega)]; rfl
    simp only [el, hh, Bool.not_false, Bool.or_true, if_true]
    rfl
  | cons c rest =>
    have hh : (SVal.array e sh hn).obs.has (.at (uintOfNat n) .nil) = true := by
      show Option.isSome ((some _).bind _) = true
      rw [Option.bind_some, SVal.findM_at', hs]
      simp only [uintOfNat_val hn, Int.natCast_nonneg, if_true, Int.toNat_natCast]
      rw [List.getElem?_append_right (by omega), hl, Nat.sub_self, List.getElem?_cons_zero,
        Option.bind_some, SVal.findM_nil']; rfl
    simp only [el, hh, Bool.not_true, Bool.or_false]
    cases hp : E.isPrimitive with
    | true => simp only [pushSlot, hp, if_true]
    | false =>
      simp only [pushSlot, hp, Bool.false_eq_true, if_false]
      have hc : (SVal.array e sh hn).obs.find (.at (uintOfNat n) .nil) = c.obs := by
        rw [SVal.obs_find, SVal.findM_at_nil, hs]
        simp only [uintOfNat_val hn, Int.natCast_nonneg, if_true, Int.toNat_natCast]
        rw [List.getElem?_append_right (by omega), hl, Nat.sub_self, List.getElem?_cons_zero]
        rfl
      rw [TVal.pushA, el, ← hc, Obs.save_find]

/-- **The bridge of `pushSlot`**: one more live element, its slot as it is. -/
theorem obs_push_slot {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))}
    (h : st.push r some = some st') : st'.obs = st.obs.extend (.ref r) := by
  obtain ⟨n, e, sh, hn, x', h', hf, hx, hs⟩ := push_some h
  cases hx
  rw [obs_save hs, Obs.extend, obs_find_some hf]
  exact congrArg _ (obs_extendArr e sh hn h')

/-- **The bridge of a push** as a place (`pushPlace`): `extend`'s. -/
theorem obs_pushPlace {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))}
    {k : PrimTy.uint.Denote} (h : st.pushPlace r = some (st', k)) :
    st'.obs = st.obs.extend (.ref r) :=
  obs_push_slot (push_of_pushPlace h)

/-- **The bridge of a pop**: the last element past the end, reset unless
`keep`. -/
theorem obs_pop {E : Ty} {st st' : Storage C} {keep : Bool} {r : SRef C (.ref (.array E))}
    (h : st.pop keep r = some st') : st'.obs = st.obs.pop keep (.ref r) := by
  unfold Storage.pop at h
  cases hf : st.find r with
  | none => simp only [hf, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some a =>
    cases a with
    | array e sh hn =>
      rename_i n
      simp only [hf, Option.bind_eq_bind, Option.bind_some, SVal.view_array] at h
      split at h
      · cases h
      · rename_i last tl hrev
        rw [obs_save h, Obs.pop, obs_find_some hf]
        have hl : e.toList.length = n := SVec.length_toList e
        have hne : e.toList ≠ [] := fun he => by simp only [he, List.reverse_nil, reduceCtorEq] at hrev
        have he : e.toList = tl.reverse ++ [last] := by
          rw [← List.reverse_reverse e.toList, hrev, List.reverse_cons]
        have hlast : e.toList.dropLast ++ [last] = e.toList := by
          rw [he, List.dropLast_concat]
        have hpos : n ≠ 0 := by intro h0; rw [← hl] at h0; exact hne (List.eq_nil_of_length_eq_zero h0)
        have el : (SVal.array e sh hn).obs.len .nil = n := rfl
        have hdl : (e.toList.dropLast).length = n - 1 := by rw [List.length_dropLast, hl]
        simp only [TVal.popA, el, hpos, if_false]
        cases keep with
        | true =>
          simp only [if_true]
          congr 1
          have hx := SVal.obs_array_setLen e sh hn (SVec.ofList e.toList.dropLast)
            (SList.ofList (last :: sh.toList)) (by rw [hdl]; omega)
            (by rw [SVec.toList_ofList, SList.toList_ofList, ← List.singleton_append,
              ← List.append_assoc, hlast])
          exact hx.trans (congrArg _ hdl)
        | false =>
          simp only [Bool.false_eq_true, if_false]
          have hk : n - 1 < (e.toList ++ sh.toList).length := by
            rw [List.length_append, hl]; omega
          have hc : (SVal.array e sh hn).obs.find (.at (uintOfNat (n - 1)) .nil) = last.obs := by
            rw [SVal.obs_find, SVal.findM_at_nil]
            simp only [uintOfNat_val (show n - 1 < 2 ^ 256 by omega), Int.natCast_nonneg, if_true,
              Int.toNat_natCast]
            rw [List.getElem?_append_left (by rw [hl]; omega), ← hlast,
              List.getElem?_append_right (by omega), hdl, Nat.sub_self, List.getElem?_cons_zero]
            rfl
          rw [hc, ← SVal.obs_defaultOf]
          congr 1
          have hx := SVal.obs_array_set e sh hn (SVec.ofList e.toList.dropLast)
            (SList.ofList (last.defaultOf :: sh.toList)) (by rw [hdl]; omega) (n - 1) last.defaultOf hk (by omega)
            (by rw [SVec.toList_ofList, SList.toList_ofList, show e.toList ++ sh.toList =
              e.toList.dropLast ++ (last :: sh.toList) by
                rw [← List.singleton_append, ← List.append_assoc, hlast],
              List.set_append_right _ _ (by omega), hdl, Nat.sub_self, List.set_cons_zero])
          exact hx.trans (congrArg _ hdl)

end Storage


/-! ### Laws of the operations -/

theorem TVal.ofWord_word_nil {P : PrimTy} (x : P.Denote) : (TVal.ofWord x).word .nil = x := rfl

namespace Obs

variable {L : Ty → Type} [ObsLoc L]

/-- **`findOnSave`** of a copy at a word: the word written. -/
theorem copyTo_word_same (o : Obs L) {P : PrimTy} (p : L (.prim P)) (v : TVal (.prim P)) :
    (o.copyTo p v).word p = v.word .nil := by
  rw [copyTo, save_word_same]; rfl

/-- **`selectOnSaveEmptySize`** of a copy: the length where it was saved is
the copy's. -/
theorem copyTo_len_same (o : Obs L) {E : Ty} (p : L (.ref (.array E)))
    (v : TVal (.ref (.array E))) : (o.copyTo p v).len p = v.len .nil := by
  have e : (o.save p (TVal.overlay (o.find p) v)).len (ObsLoc.app p .nil) =
      (TVal.overlay (o.find p) v).len .nil := by
    simp only [save, ObsLoc.strip?_app]
  rw [ObsLoc.app_nil] at e
  rw [copyTo, e]
  rfl

/-- **`findOnDelAt`**: a word deleted reads its default. -/
theorem delAt_word_same (o : Obs L) {P : PrimTy} (p : L (.prim P)) :
    (o.delAt p).word p = PrimTy.dflt P := by
  rw [delAt, save_word_same]; rfl

/-- Below a delete, the delete's reading. -/
theorem delAt_word_below (o : Obs L) {U : Ty} (p : L U) {P : PrimTy} (r : Path U (.prim P)) :
    (o.delAt p).word (ObsLoc.app p r) = TVal.delR (Comp.word P) (o.find p) r := by
  rw [delAt, save_word_below]; rfl

/-! The laws by solkey's taclet names, as `sol_rw` reads them: a frame's
premise the decidable `(ObsLoc.strip? p q).isNone`. -/

/-- **`findOnSave`**. -/
theorem findOnSave (o : Obs L) {P : PrimTy} (p : L (.prim P)) (v : TVal (.prim P)) :
    (o.copyTo p v).word p = v.word .nil := copyTo_word_same o p v

/-- **`findOnSavePrefix`**: a read above a save sees the save made below
it. -/
theorem findOnSavePrefix (o : Obs L) {U V : Ty} (q : L U) (r : Path U V) (v : TVal V) :
    (o.copyTo (ObsLoc.app q r) v).find q = (o.find q).copyTo r v := by
  rw [copyTo, copyTo, find_save_below, find_find]

/-- **`findOnSaveFrame`** (solkey's `selectOnSaveCons` `\else`). -/
theorem findOnSaveFrame (o : Obs L) {U : Ty} {p : L U} {P : PrimTy} {q : L (.prim P)}
    (v : TVal U) (h : (ObsLoc.strip? p q).isNone = true) : (o.copyTo p v).word q = o.word q :=
  save_word_frame _ _ (Option.isNone_iff_eq_none.1 h)

/-- **`findOnDelAt`**. -/
theorem findOnDelAt (o : Obs L) {P : PrimTy} (p : L (.prim P)) :
    (o.delAt p).word p = PrimTy.dflt P := delAt_word_same o p

/-- **`findOnDelAtFrame`**. -/
theorem findOnDelAtFrame (o : Obs L) {U : Ty} {p : L U} {P : PrimTy} {q : L (.prim P)}
    (h : (ObsLoc.strip? p q).isNone = true) : (o.delAt p).word q = o.word q :=
  save_word_frame _ _ (Option.isNone_iff_eq_none.1 h)

/-- **`lenOnSaveFrame`**. -/
theorem lenOnSaveFrame (o : Obs L) {U : Ty} {p : L U} {E : Ty} {q : L (.ref (.array E))}
    (v : TVal U) (h : (ObsLoc.strip? p q).isNone = true) : (o.copyTo p v).len q = o.len q :=
  save_len_frame _ _ (Option.isNone_iff_eq_none.1 h)

/-- **`lenOnDelAtFrame`**. -/
theorem lenOnDelAtFrame (o : Obs L) {U : Ty} {p : L U} {E : Ty} {q : L (.ref (.array E))}
    (h : (ObsLoc.strip? p q).isNone = true) : (o.delAt p).len q = o.len q :=
  save_len_frame _ _ (Option.isNone_iff_eq_none.1 h)

/-- **`findOnPushFrame`**. -/
theorem findOnPushFrame (o : Obs L) {E : Ty} {p : L (.ref (.array E))} {P : PrimTy}
    {q : L (.prim P)} (x : TVal E) (h : (ObsLoc.strip? p q).isNone = true) :
    (o.push p x).word q = o.word q :=
  save_word_frame _ _ (Option.isNone_iff_eq_none.1 h)

/-- **`findOnPopFrame`**. -/
theorem findOnPopFrame (o : Obs L) (keep : Bool) {E : Ty} {p : L (.ref (.array E))} {P : PrimTy}
    {q : L (.prim P)} (h : (ObsLoc.strip? p q).isNone = true) :
    (o.pop keep p).word q = o.word q :=
  save_word_frame _ _ (Option.isNone_iff_eq_none.1 h)

end Obs

/-! ### Under a `select` -/

theorem SRef.under_append {C : Contract} {s r : Name} {U W : Ty} (h : C.rootType r = some (.ref (.struct s)))
    (q : SRef (Contract.ofStruct s) U) (p : Path U W) :
    (q.append p).under h = (q.under h).append p := by
  simp only [SRef.under, SRef.append, Path.append_field]

theorem SLoc.under_app {C : Contract} {s r : Name} {U W : Ty} (h : C.rootType r = some (.ref (.struct s)))
    (l : SLoc (Contract.ofStruct s) U) (p : Path U W) :
    (ObsLoc.app l p).under h = ObsLoc.app (l.under h) p := by
  cases l with
  | ref q => exact congrArg SLoc.ref (SRef.under_append h q p)
  | dangling => rfl

theorem SRef.strip?_under {C : Contract} {s r : Name} {U W : Ty}
    (h : C.rootType r = some (.ref (.struct s))) (q : SRef (Contract.ofStruct s) U)
    (q' : SRef (Contract.ofStruct s) W) : (q.under h).strip? (q'.under h) = q.strip? q' := by
  rcases q with ⟨n, hn, qp⟩
  rcases q' with ⟨n', hn', qp'⟩
  unfold SRef.strip? SRef.under
  rw [dif_pos rfl]
  by_cases e : n = n'
  · subst e
    obtain rfl : _ = _ := Option.some.inj (hn.symm.trans hn')
    simp only [dite_true, Path.strip?]
  · simp only [Path.strip?, e, dite_false]

theorem SRef.strip?_under_ne {C : Contract} {s r s' r' : Name} {U W : Ty}
    (h : C.rootType r = some (.ref (.struct s))) (h' : C.rootType r' = some (.ref (.struct s')))
    (hne : r' ≠ r) (q : SRef (Contract.ofStruct s') U) (q' : SRef (Contract.ofStruct s) W) :
    (q.under h').strip? (q'.under h) = none := by
  unfold SRef.strip? SRef.under
  rw [dif_neg hne]

/-- A `select`'s read below a member: the read below the member's path. -/
theorem Obs.select_find {C : Contract} {s r : Name} (o : TSto C)
    (h : C.rootType r = some (.ref (.struct s))) {U : Ty} (l : SLoc (Contract.ofStruct s) U) :
    (o.select h).find l = o.find (l.under h) := by
  apply Obs.ext <;> intro _ q <;> simp only [Obs.find, Obs.select, SLoc.under_app]

/-- **`selectOnSaveCons`** at the member saved: the save seen from the root
is a save at the member path. -/
theorem Obs.select_save {C : Contract} {s r : Name} (o : TSto C)
    (h : C.rootType r = some (.ref (.struct s))) {U : Ty} (l : SLoc (Contract.ofStruct s) U)
    (v : TVal U) : (o.save (l.under h) v).select h = (o.select h).save l v := by
  have e : ∀ {W : Ty} (q : SLoc (Contract.ofStruct s) W),
      ObsLoc.strip? (l.under h) (q.under h) = ObsLoc.strip? l q := by
    intro W q
    cases l <;> cases q
    · exact SRef.strip?_under h _ _
    · rfl
    · rfl
    · rfl
  apply Obs.ext <;> intro _ q <;> simp only [Obs.select, Obs.save, e]

/-- **`selectOnSaveCons`** away from the member: a save under another root
is not seen from `r`. -/
theorem Obs.select_save_ne {C : Contract} {s r s' r' : Name} (o : TSto C)
    (h : C.rootType r = some (.ref (.struct s))) (h' : C.rootType r' = some (.ref (.struct s')))
    (hne : r' ≠ r) {U : Ty} (q' : SRef (Contract.ofStruct s') U) (v : TVal U) :
    (o.save ((SLoc.ref q').under h') v).select h = o.select h := by
  have e : ∀ {W : Ty} (q : SLoc (Contract.ofStruct s) W),
      ObsLoc.strip? ((SLoc.ref q').under h') (q.under h) = none := by
    intro W q
    cases q
    · exact SRef.strip?_under_ne h h' hne _ _
    · rfl
  apply Obs.ext <;> intro _ q <;> simp only [Obs.select, Obs.save, e]

theorem Obs.select_copyTo {C : Contract} {s r : Name} (o : TSto C)
    (h : C.rootType r = some (.ref (.struct s))) {U : Ty} (l : SLoc (Contract.ofStruct s) U)
    (v : TVal U) : (o.copyTo (l.under h) v).select h = (o.select h).copyTo l v := by
  rw [Obs.copyTo, Obs.copyTo, Obs.select_save, Obs.select_find]

theorem Obs.select_delAt {C : Contract} {s r : Name} (o : TSto C)
    (h : C.rootType r = some (.ref (.struct s))) {U : Ty} (l : SLoc (Contract.ofStruct s) U) :
    (o.delAt (l.under h)).select h = (o.select h).delAt l := by
  rw [Obs.delAt, Obs.delAt, Obs.select_save, Obs.select_find]

theorem Obs.select_copyTo_ne {C : Contract} {s r s' r' : Name} (o : TSto C)
    (h : C.rootType r = some (.ref (.struct s))) (h' : C.rootType r' = some (.ref (.struct s')))
    (hne : r' ≠ r) {U : Ty} (q' : SRef (Contract.ofStruct s') U) (v : TVal U) :
    (o.copyTo ((SLoc.ref q').under h') v).select h = o.select h := by
  rw [Obs.copyTo, Obs.select_save_ne o h h' hne]

theorem Obs.select_delAt_ne {C : Contract} {s r s' r' : Name} (o : TSto C)
    (h : C.rootType r = some (.ref (.struct s))) (h' : C.rootType r' = some (.ref (.struct s')))
    (hne : r' ≠ r) {U : Ty} (q' : SRef (Contract.ofStruct s') U) :
    (o.delAt ((SLoc.ref q').under h')).select h = o.select h := by
  rw [Obs.delAt, Obs.select_save_ne o h h' hne]

end Solidity
