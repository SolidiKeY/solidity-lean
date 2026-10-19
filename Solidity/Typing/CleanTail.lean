import Solidity.Typing.Values

namespace Solidity

open Semantics (lookupBy)

def ordinaryDefaultFold : Fold where
  V _ := Prop
  F _ := Prop
  L _ := Prop
  W _ _ := Prop
  M _ _ := Prop
  prim := fun {p} v => v = PrimTy.dflt p
  struct := fun _ ih => ih
  array := fun {_} {n} _ _ _ _ ish => n = 0 ∧ ish
  fixed := fun _ ie => ie
  map := fun _ _ _ _ => True
  fnil := True
  fcons := fun _ _ iv ir => iv ∧ ir
  lnil := True
  lcons := fun _ _ iv ir => iv ∧ ir
  wnil := True
  wcons := fun _ _ iv ir => iv ∧ ir
  mnil := True
  mcons := fun _ _ _ _ _ => True

def SVal.OrdinaryDefault {T : Ty} (v : SVal T) : Prop := v.fold ordinaryDefaultFold
def SFields.OrdinaryDefault {fs : List (Name × Ty)} (v : SFields fs) : Prop :=
  v.fold ordinaryDefaultFold
def SList.OrdinaryDefault {T : Ty} (v : SList T) : Prop := v.fold ordinaryDefaultFold
def SVec.OrdinaryDefault {T : Ty} {n : Nat} (v : SVec T n) : Prop :=
  v.fold ordinaryDefaultFold

theorem SVal.ordinaryDefault_prim {p : PrimTy} (v : p.Denote) :
    (SVal.prim v).OrdinaryDefault ↔ v = PrimTy.dflt p := Iff.rfl

theorem SVal.ordinaryDefault_struct {s : Name} (fs : SFields (Semantics.structDef s)) :
    (SVal.struct fs).OrdinaryDefault ↔ fs.OrdinaryDefault := Iff.rfl

theorem SVal.ordinaryDefault_array {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E)
    (hn : n < 2 ^ 256) :
    (SVal.array e sh hn).OrdinaryDefault ↔ n = 0 ∧ sh.OrdinaryDefault := Iff.rfl

theorem SVal.ordinaryDefault_fixed {E : Ty} {n : Nat} (e : SVec E n) :
    (SVal.fixed e).OrdinaryDefault ↔ e.OrdinaryDefault := Iff.rfl

theorem SVal.ordinaryDefault_map {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V) :
    (SVal.map m d).OrdinaryDefault := trivial

theorem SFields.ordinaryDefault_nil : SFields.nil.OrdinaryDefault := trivial

theorem SFields.ordinaryDefault_cons {f : Name} {T : Ty} {fs : List (Name × Ty)}
    (v : SVal T) (rest : SFields fs) :
    (SFields.cons (f := f) v rest).OrdinaryDefault ↔
      v.OrdinaryDefault ∧ rest.OrdinaryDefault := Iff.rfl

theorem SList.ordinaryDefault_nil {E : Ty} : (SList.nil (E := E)).OrdinaryDefault := trivial

theorem SList.ordinaryDefault_cons {E : Ty} (v : SVal E) (rest : SList E) :
    (SList.cons v rest).OrdinaryDefault ↔ v.OrdinaryDefault ∧ rest.OrdinaryDefault := Iff.rfl

theorem SVec.ordinaryDefault_nil {E : Ty} : (SVec.nil (E := E)).OrdinaryDefault := trivial

theorem SVec.ordinaryDefault_cons {E : Ty} {n : Nat} (v : SVal E) (rest : SVec E n) :
    (SVec.cons v rest).OrdinaryDefault ↔ v.OrdinaryDefault ∧ rest.OrdinaryDefault := Iff.rfl

def cleanTailH : Hered where
  arr := fun _ sh => sh.OrdinaryDefault
  fix := fun _ _ => True
  map := fun _ => fun {_} _ _ => True

def SVal.CleanTail {T : Ty} (v : SVal T) : Prop := v.All cleanTailH
def SFields.CleanTail {fs : List (Name × Ty)} (v : SFields fs) : Prop := v.All cleanTailH
def Storage.CleanTail {C : Contract} (st : Storage C) : Prop := st.All cleanTailH

theorem SList.ordinaryDefault_iff {E : Ty} : (sh : SList E) →
    (sh.OrdinaryDefault ↔ ∀ v ∈ sh.toList, v.OrdinaryDefault)
  | .nil => by simp only [SList.OrdinaryDefault, SList.fold, ordinaryDefaultFold,
      SList.toList_nil, List.not_mem_nil, false_implies, implies_true]
  | .cons v rest => by
    rw [SList.ordinaryDefault_cons, SList.ordinaryDefault_iff rest, SList.toList_cons]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem SVec.ordinaryDefault_iff {E : Ty} : {n : Nat} → (e : SVec E n) →
    (e.OrdinaryDefault ↔ ∀ v ∈ e.toList, v.OrdinaryDefault)
  | _, .nil => by simp only [SVec.OrdinaryDefault, SVec.fold, ordinaryDefaultFold,
      SVec.toList_nil, List.not_mem_nil, false_implies, implies_true]
  | _, .cons v rest => by
    rw [SVec.ordinaryDefault_cons, SVec.ordinaryDefault_iff rest, SVec.toList_cons]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem SList.ordinaryDefault_ofList {E : Ty} (xs : List (SVal E)) :
    (SList.ofList xs).OrdinaryDefault ↔ ∀ v ∈ xs, v.OrdinaryDefault := by
  rw [SList.ordinaryDefault_iff, SList.toList_ofList]

mutual
theorem SVal.defaultOf_ordinaryDefault : {T : Ty} → (v : SVal T) → v.CleanTail →
    v.defaultOf.OrdinaryDefault
  | _, .prim v, _ => by
    rw [SVal.defaultOf_prim, SVal.ordinaryDefault_prim]
  | _, .struct fs, h => by
    rw [SVal.defaultOf_struct, SVal.ordinaryDefault_struct]
    exact SFields.defaultOf_ordinaryDefault fs
      (by simpa only [SVal.CleanTail, SVal.All_struct] using h)
  | _, .array e sh hn, h => by
    rw [SVal.defaultOf_array, SVal.ordinaryDefault_array]
    have hc : sh.OrdinaryDefault ∧ e.All cleanTailH ∧ sh.All cleanTailH := by
      simpa only [SVal.CleanTail, SVal.All_array, cleanTailH] using h
    refine ⟨rfl, ?_⟩
    rw [SList.ordinaryDefault_ofList]
    exact (List.forall_mem_append).2
      ⟨(SVec.ordinaryDefault_iff _).1 (SVec.defaultOf_ordinaryDefault e hc.2.1),
        (SList.ordinaryDefault_iff _).1 hc.1⟩
  | _, .fixed e, h => by
    rw [SVal.defaultOf_fixed, SVal.ordinaryDefault_fixed]
    have hc : True ∧ e.All cleanTailH := by
      simpa only [SVal.CleanTail, SVal.All_fixed, cleanTailH] using h
    exact SVec.defaultOf_ordinaryDefault e hc.2
  | _, .map m d, _ => by
    rw [SVal.defaultOf_map]
    exact SVal.ordinaryDefault_map m d

theorem SFields.defaultOf_ordinaryDefault : {fs : List (Name × Ty)} → (v : SFields fs) →
    v.All cleanTailH → v.defaultOf.OrdinaryDefault
  | _, .nil, _ => by rw [SFields.defaultOf_nil]; exact SFields.ordinaryDefault_nil
  | _, .cons v rest, h => by
    rw [SFields.defaultOf_cons, SFields.ordinaryDefault_cons]
    have hc : v.All cleanTailH ∧ rest.All cleanTailH := by
      simpa only [SFields.All_cons] using h
    exact ⟨SVal.defaultOf_ordinaryDefault v hc.1,
      SFields.defaultOf_ordinaryDefault rest hc.2⟩

theorem SVec.defaultOf_ordinaryDefault : {E : Ty} → {n : Nat} → (e : SVec E n) →
    e.All cleanTailH → e.defaultOf.OrdinaryDefault
  | _, _, .nil, _ => by rw [SVec.defaultOf_nil]; exact SVec.ordinaryDefault_nil
  | _, _, .cons v rest, h => by
    rw [SVec.defaultOf_cons, SVec.ordinaryDefault_cons]
    have hc : v.All cleanTailH ∧ rest.All cleanTailH := by
      simpa only [SVec.All_cons] using h
    exact ⟨SVal.defaultOf_ordinaryDefault v hc.1,
      SVec.defaultOf_ordinaryDefault rest hc.2⟩
end

theorem SVal.dflt_cleanTail (T : Ty) : (SVal.dflt T).CleanTail :=
  SVal.dflt_all (P := cleanTailH) (fun _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) T

theorem Storage.init_cleanTail (C : Contract) : (Storage.init C).CleanTail :=
  SFields.dflt_all (P := cleanTailH) (fun _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) C.vars

theorem SVal.dflt_ordinaryDefault (T : Ty) : (SVal.dflt T).OrdinaryDefault := by
  rw [← SVal.defaultOf_dflt T]
  exact SVal.defaultOf_ordinaryDefault _ (SVal.dflt_cleanTail T)

theorem pushSlot_ordinaryDefault {E : Ty} (xs : List (SVal E))
    (h : ∀ v ∈ xs, v.OrdinaryDefault) : (pushSlot E xs).1.OrdinaryDefault := by
  cases xs with
  | nil => exact SVal.dflt_ordinaryDefault E
  | cons v rest =>
    change (if E.isPrimitive then SVal.dflt E else v).OrdinaryDefault
    split
    · exact SVal.dflt_ordinaryDefault E
    · exact h v List.mem_cons_self

theorem SVal.cleanTail_shadow {E : Ty} {n : Nat} {e : SVec E n} {sh : SList E}
    {hn : n < 2 ^ 256} (h : (SVal.array e sh hn).CleanTail) :
    ∀ v ∈ sh.toList, v.OrdinaryDefault :=
  (SList.ordinaryDefault_iff sh).1
    ((by simpa only [SVal.CleanTail, SVal.All_array, cleanTailH] using h :
      sh.OrdinaryDefault ∧ e.All cleanTailH ∧ sh.All cleanTailH).1)

theorem SVal.emptyPush_ordinaryDefault {E : Ty} {n : Nat} {e : SVec E n} {sh : SList E}
    {hn : n < 2 ^ 256} (h : (SVal.array e sh hn).CleanTail) :
    (pushSlot E sh.toList).1.OrdinaryDefault :=
  pushSlot_ordinaryDefault sh.toList (SVal.cleanTail_shadow h)

theorem cleanTailH_delOK : cleanTailH.DelOK := by
  intro E n e sh hsh he
  change (SList.ofList (e.defaultOf.toList ++ sh.toList)).OrdinaryDefault
  rw [SList.ordinaryDefault_ofList]
  exact (List.forall_mem_append).2
    ⟨(SVec.ordinaryDefault_iff _).1 (SVec.defaultOf_ordinaryDefault e he),
      (SList.ordinaryDefault_iff _).1 hsh⟩

theorem SVal.defaultOf_cleanTail {T : Ty} {v : SVal T} (h : v.CleanTail) :
    v.defaultOf.CleanTail :=
  SVal.defaultOf_all cleanTailH_delOK h

theorem SVal.find_cleanTail {T U : Ty} {v : SVal T} {w : SVal U} (p : Path T U)
    (hv : v.CleanTail) (hread : v.find p = some w) : w.CleanTail :=
  SVal.find_all p hv hread

/-! ## Clean tails, as the observations show them

The Theory reads a storage by its observations (`Storage.obs`,
`Theory/Typed/Obs.lean`), and they do not show every slot of the typed
value (a mapping's shadowed entry, a default every key covers): so what
`cleanTail(storage)` denotes there is what they show, `TSto.CleanTails`,
which `Storage.CleanTail` implies (`Storage.cleanTails_obs`). -/

/-- A path with no mapping key step. -/
def Path.KeyFree : {T U : Ty} → Path T U → Prop
  | _, _, .nil => True
  | _, _, .field _ p => p.KeyFree
  | _, _, .at _ p => p.KeyFree
  | _, _, .atF _ p => p.KeyFree
  | _, _, .key _ _ => False

theorem Path.keyFree_append : {T U W : Ty} → (p : Path T U) → (q : Path U W) →
    p.KeyFree → q.KeyFree → (p.append q).KeyFree
  | _, _, _, .nil, _, _, hq => by rw [Path.append_nil]; exact hq
  | _, _, _, .field h p, q, hp, hq => by
    rw [Path.append_field]; exact Path.keyFree_append p q hp hq
  | _, _, _, .at i p, q, hp, hq => by
    rw [Path.append_at]; exact Path.keyFree_append p q hp hq
  | _, _, _, .atF i p, q, hp, hq => by
    rw [Path.append_atF]; exact Path.keyFree_append p q hp hq
  | _, _, _, .key _ _, _, hp, _ => hp.elim

/-- **A read past an array's live end**, in the observations `o`: `r` goes
through a dynamic array `a` at an index at or past `a`'s live length, and
on along no mapping key. -/
def SRef.Shadowed {C : Contract} (o : TSto C) {T : Ty} (r : SRef C T) : Prop :=
  ∃ (E : Ty) (a : SRef C (.ref (.array E))) (i : PrimTy.uint.Denote) (rest : Path E T),
    rest.KeyFree ∧ o.len (.ref a) ≤ i.1.toNat ∧ r = a.append (.at i rest)

/-- **Clean tails, observed**: a read past an array's live end, along no
mapping key, shows the default word and the length `0`. -/
def TSto.CleanTails {C : Contract} (o : TSto C) : Prop :=
  (∀ {P : PrimTy} (r : SRef C (.prim P)), r.Shadowed o → o.word (.ref r) = PrimTy.dflt P) ∧
  (∀ {E : Ty} (r : SRef C (.ref (.array E))), r.Shadowed o → o.len (.ref r) = 0)

theorem SRef.Shadowed.append {C : Contract} {o : TSto C} {T U : Ty} {r : SRef C T}
    (h : r.Shadowed o) (q : Path T U) (hq : q.KeyFree) : (r.append q).Shadowed o := by
  obtain ⟨E, a, i, rest, hk, hl, rfl⟩ := h
  refine ⟨E, a, i, rest.append q, Path.keyFree_append rest q hk hq, hl, ?_⟩
  rw [SRef.append_append, Path.append_at]

theorem SRef.shadowed_index {C : Contract} {o : TSto C} {E : Ty}
    (a : SRef C (.ref (.array E))) (i : PrimTy.uint.Denote) (h : o.len (.ref a) ≤ i.1.toNat) :
    (a.index (.arr .dyn) i).Shadowed o :=
  ⟨E, a, i, .nil, trivial, h, by rw [SRef.index, Path.index_dyn]⟩

theorem SFields.ordinaryDefault_get {f : Name} : {fs : List (Name × Ty)} → {T : Ty} →
    {x : SFields fs} → (h : lookupBy f fs = some T) → x.OrdinaryDefault →
    (x.get h).OrdinaryDefault
  | [], _, .nil, h, _ => by simp only [lookupBy, reduceCtorEq] at h
  | (f', T') :: fs, T, .cons v rest, h, hx => by
    rw [SFields.ordinaryDefault_cons] at hx
    rw [SFields.get_cons]
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [e, dite_true]
      exact hx.1
    · simp only [e, dite_false]
      exact SFields.ordinaryDefault_get _ hx.2

/-- An ordinary default read along no mapping key is one. -/
theorem SVal.ordinaryDefault_findM : {T U : Ty} → (x : SVal T) → (p : Path T U) →
    x.OrdinaryDefault → p.KeyFree → ∀ w, x.findM p = some w → w.OrdinaryDefault
  | _, _, x, .nil, hx, _, w, h => by
    have : x = w := by cases x <;> (simp only [SVal.findM, Option.some.injEq] at h; exact h)
    exact this ▸ hx
  | _, _, .struct fs, .field hf p, hx, hp, w, h => by
    simp only [SVal.findM] at h
    exact SVal.ordinaryDefault_findM _ p
      (SFields.ordinaryDefault_get hf ((SVal.ordinaryDefault_struct fs).1 hx)) hp w h
  | _, _, .array e sh _, .at i p, hx, hp, w, h => by
    obtain ⟨rfl, hsh⟩ := (SVal.ordinaryDefault_array e sh _).1 hx
    simp only [SVal.findM] at h
    split at h
    · rename_i y hy
      have hy' : y ∈ e.toList ++ sh.toList := List.mem_of_getElem? hy
      have hmem : y ∈ sh.toList := by
        cases e
        simpa only [SVec.toList_nil, List.nil_append] using hy'
      exact SVal.ordinaryDefault_findM y p ((SList.ordinaryDefault_iff sh).1 hsh y hmem) hp w h
    · cases h
  | _, _, .fixed e, .atF i p, hx, hp, w, h => by
    simp only [SVal.findM] at h
    split at h
    · rename_i y hy
      exact SVal.ordinaryDefault_findM y p
        ((SVec.ordinaryDefault_iff e).1 ((SVal.ordinaryDefault_fixed e).1 hx) y
          (List.mem_of_getElem? hy)) hp w h
    · cases h
  | _, _, .map _ _, .key _ _, _, hp, _, _ => hp.elim

/-- Under clean tails, what a read past an array's live end finds is an
ordinary default. -/
theorem Storage.shadowed_findM {C : Contract} {st : Storage C} (hst : st.CleanTail) {T : Ty}
    {r : SRef C T} (hs : r.Shadowed st.obs) :
    ∀ w, (st.get r.hroot).findM r.path = some w → w.OrdinaryDefault := by
  obtain ⟨E, a, i, rest, hk, hl, rfl⟩ := hs
  intro w hw
  change (st.get a.hroot).findM (a.path.append (.at i rest)) = some w at hw
  rw [SVal.findM_append] at hw
  cases hy : (st.get a.hroot).findM a.path with
  | none => rw [hy] at hw; cases hw
  | some y =>
    rw [hy, Option.bind_some] at hw
    have hyc : y.CleanTail :=
      SVal.findM_all (P := cleanTailH) a.path (SFields.all_get a.hroot hst) hy
    cases y with
    | array e sh hn =>
      rename_i n
      have hn' : n ≤ i.1.toNat := by
        have : st.obs.len (.ref a) = n := by
          show SVal.lenOf ((st.get a.hroot).findM a.path) = n
          rw [hy]; rfl
        omega
      simp only [SVal.findM] at hw
      split at hw
      · rename_i x hx
        have hlen : e.toList.length ≤ i.1.toNat := by rw [SVec.length_toList]; exact hn'
        rw [List.getElem?_append_right hlen] at hx
        exact SVal.ordinaryDefault_findM x rest
          (SVal.cleanTail_shadow hyc x (List.mem_of_getElem? hx)) hk w hw
      · cases hw

/-- **Clean tails show**: a storage with clean tails reads as one. -/
theorem Storage.cleanTails_obs {C : Contract} {st : Storage C} (hst : st.CleanTail) :
    TSto.CleanTails st.obs := by
  refine ⟨fun {P} r hs => ?_, fun {E} r hs => ?_⟩
  · show SVal.wordOf ((st.get r.hroot).findM r.path) = PrimTy.dflt P
    cases hw : (st.get r.hroot).findM r.path with
    | none => rfl
    | some w =>
      have hd := Storage.shadowed_findM hst hs w hw
      cases w with
      | prim v => exact (SVal.ordinaryDefault_prim v).1 hd
  · show SVal.lenOf ((st.get r.hroot).findM r.path) = 0
    cases hw : (st.get r.hroot).findM r.path with
    | none => rfl
    | some w =>
      have hd := Storage.shadowed_findM hst hs w hw
      cases w with
      | array e sh hn => exact ((SVal.ordinaryDefault_array e sh hn).1 hd).1

/-! ## The test `cleanTail(storage)` runs -/

mutual
theorem SVal.ordinaryDefaultB_iff : {T : Ty} → (v : SVal T) →
    v.fold ordinaryDefaultBFold = true ↔ v.OrdinaryDefault
  | _, .prim _ => decide_eq_true_iff
  | _, .struct fs => SFields.ordinaryDefaultB_iff fs
  | _, @SVal.array _ n e sh _ => by
    show (n == 0 && sh.fold ordinaryDefaultBFold) = true ↔ n = 0 ∧ sh.OrdinaryDefault
    rw [Bool.and_eq_true, beq_iff_eq, SList.ordinaryDefaultB_iff sh]
  | _, .fixed e => SVec.ordinaryDefaultB_iff e
  | _, .map _ _ => iff_of_true rfl trivial

theorem SFields.ordinaryDefaultB_iff : {fs : List (Name × Ty)} → (x : SFields fs) →
    x.fold ordinaryDefaultBFold = true ↔ x.OrdinaryDefault
  | _, .nil => iff_of_true rfl trivial
  | _, .cons v rest => by
    show (v.fold ordinaryDefaultBFold && rest.fold ordinaryDefaultBFold) = true ↔
      v.OrdinaryDefault ∧ rest.OrdinaryDefault
    rw [Bool.and_eq_true, SVal.ordinaryDefaultB_iff v, SFields.ordinaryDefaultB_iff rest]

theorem SList.ordinaryDefaultB_iff : {E : Ty} → (l : SList E) →
    l.fold ordinaryDefaultBFold = true ↔ l.OrdinaryDefault
  | _, .nil => iff_of_true rfl trivial
  | _, .cons v rest => by
    show (v.fold ordinaryDefaultBFold && rest.fold ordinaryDefaultBFold) = true ↔
      v.OrdinaryDefault ∧ rest.OrdinaryDefault
    rw [Bool.and_eq_true, SVal.ordinaryDefaultB_iff v, SList.ordinaryDefaultB_iff rest]

theorem SVec.ordinaryDefaultB_iff : {E : Ty} → {n : Nat} → (l : SVec E n) →
    l.fold ordinaryDefaultBFold = true ↔ l.OrdinaryDefault
  | _, _, .nil => iff_of_true rfl trivial
  | _, _, .cons v rest => by
    show (v.fold ordinaryDefaultBFold && rest.fold ordinaryDefaultBFold) = true ↔
      v.OrdinaryDefault ∧ rest.OrdinaryDefault
    rw [Bool.and_eq_true, SVal.ordinaryDefaultB_iff v, SVec.ordinaryDefaultB_iff rest]
end

theorem cleanTailHB_decides : cleanTailHB.Decides cleanTailH :=
  ⟨fun _ sh => SList.ordinaryDefaultB_iff sh, fun _ _ => iff_of_true rfl trivial,
    fun _ _ _ _ => iff_of_true rfl trivial⟩

/-- **What `cleanTail(storage)` tests**: every array's shadow an ordinary
default. -/
theorem Storage.cleanTailB_iff {C : Contract} (st : Storage C) :
    st.cleanTailB = true ↔ st.CleanTail :=
  SFields.allB_iff cleanTailHB_decides st

end Solidity
