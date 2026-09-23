import Solidity.Semantics.Properties
import Solidity.Theory.Storage

/-!
# The two storage readers, side by side

`Update/Lower.lean` replaces a read in a derivation line by a term of the
storage theory, and has to show the interpreter reads the same thing.  These
are the laws it walks with: the interpreter's read after a write, at the four
places a read path can lie against a written one (`SemanticsProperties` has
only the same path), and the theory's reads of a deleted node.

The interpreter half is stated for a write that *succeeded*; a failed one fails
the whole update, and the lowering never looks past it.
-/

namespace Solidity
namespace Update

open Semantics SemanticsProperties Theory Theory.StValue

/-! ## Interpreter: the read after a write -/

/-- **Below the write** (and, at `r = []`, the write itself): a read that goes
through the written path reads out of the written value. -/
theorem SVal.find_save_extends {old new updated : SVal} {path : List Seg}
    (h : old.save path new = .ok updated) (r : List Seg) :
    updated.find (path ++ r) = new.find r := by
  induction path generalizing old updated with
  | nil =>
      simp [SVal.save] at h
      subst updated
      rfl
  | cons seg rest ih =>
      cases seg with
      | field name =>
          cases old <;> try { simp [SVal.save] at h }
          rename_i fields
          cases hv : lookupBy name fields with
          | none => simp [SVal.save, hv] at h
          | some old =>
              simp only [SVal.save, hv] at h
              cases hs : old.save rest new with
              | error e => rw [hs] at h; contradiction
              | ok child =>
                  rw [hs] at h
                  injection h with h'
                  subst updated
                  simp [SVal.find, lookupBy_setBy_self, ih hs]
      | «at» i =>
          cases old <;> try { simp [SVal.save] at h }
          · rename_i elems shadow
            simp only [SVal.save] at h
            split at h
            next hb =>
              cases hs : (elems.get ⟨i.toNat, hb.2⟩).save rest new with
              | error e => rw [hs] at h; contradiction
              | ok child =>
                  rw [hs] at h
                  injection h with h'
                  subst updated
                  simp [SVal.find, hb, ih hs]
            next hb => contradiction
          · rename_i entries dflt
            cases hv : lookupBy i entries with
            | none =>
                simp only [SVal.save, hv] at h
                cases hs : dflt.save rest new with
                | error e => rw [hs] at h; contradiction
                | ok child =>
                    rw [hs] at h
                    injection h with h'
                    subst updated
                    simp [SVal.find, lookupBy_setBy_self, ih hs]
            | some old =>
                simp only [SVal.save, hv] at h
                cases hs : old.save rest new with
                | error e => rw [hs] at h; contradiction
                | ok child =>
                    rw [hs] at h
                    injection h with h'
                    subst updated
                    simp [SVal.find, lookupBy_setBy_self, ih hs]

/-- **Off the write**: a read that leaves the written path does not see it.
Array lengths and a mapping's absent keys included — the written slot is the
only thing that moved. -/
theorem SVal.find_save_frame {old new updated : SVal} {path q : List Seg}
    (h : old.save path new = .ok updated) (hd : diverges path q = true) :
    updated.find q = old.find q := by
  induction path generalizing old updated q with
  | nil => simp [diverges] at hd
  | cons seg rest ih =>
      cases q with
      | nil => simp [diverges] at hd
      | cons b q' =>
          by_cases hab : seg = b
          · subst hab
            have hd' : diverges rest q' = true := by simpa [diverges] using hd
            cases seg with
            | field name =>
                cases old <;> try { simp [SVal.save] at h }
                rename_i fields
                cases hv : lookupBy name fields with
                | none => simp [SVal.save, hv] at h
                | some old =>
                    simp only [SVal.save, hv] at h
                    cases hs : old.save rest new with
                    | error e => rw [hs] at h; contradiction
                    | ok child =>
                        rw [hs] at h
                        injection h with h'
                        subst updated
                        simp [SVal.find, lookupBy_setBy_self, hv, ih hs hd']
            | «at» i =>
                cases old <;> try { simp [SVal.save] at h }
                · rename_i elems shadow
                  simp only [SVal.save] at h
                  split at h
                  next hb =>
                    cases hs : (elems.get ⟨i.toNat, hb.2⟩).save rest new with
                    | error e => rw [hs] at h; contradiction
                    | ok child =>
                        rw [hs] at h
                        injection h with h'
                        subst updated
                        have := ih hs hd'
                        simp only [List.get_eq_getElem] at this
                        simp [SVal.find, hb, this]
                  next hb => contradiction
                · rename_i entries dflt
                  cases hv : lookupBy i entries with
                  | none =>
                      simp only [SVal.save, hv] at h
                      cases hs : dflt.save rest new with
                      | error e => rw [hs] at h; contradiction
                      | ok child =>
                          rw [hs] at h
                          injection h with h'
                          subst updated
                          simp [SVal.find, lookupBy_setBy_self, hv, ih hs hd']
                  | some old =>
                      simp only [SVal.save, hv] at h
                      cases hs : old.save rest new with
                      | error e => rw [hs] at h; contradiction
                      | ok child =>
                          rw [hs] at h
                          injection h with h'
                          subst updated
                          simp [SVal.find, lookupBy_setBy_self, hv, ih hs hd']
          · cases seg with
            | field name =>
                cases old <;> try { simp [SVal.save] at h }
                rename_i fields
                cases hv : lookupBy name fields with
                | none => simp [SVal.save, hv] at h
                | some old =>
                    simp only [SVal.save, hv] at h
                    cases hs : old.save rest new with
                    | error e => rw [hs] at h; contradiction
                    | ok child =>
                        rw [hs] at h
                        injection h with h'
                        subst updated
                        cases b with
                        | field name2 =>
                            have hne : name2 ≠ name := fun e => hab (by rw [e])
                            simp [SVal.find, lookupBy_setBy_ne hne]
                        | «at» j => simp [SVal.find]
            | «at» i =>
                cases old <;> try { simp [SVal.save] at h }
                · rename_i elems shadow
                  simp only [SVal.save] at h
                  split at h
                  next hb =>
                    cases hs : (elems.get ⟨i.toNat, hb.2⟩).save rest new with
                    | error e => rw [hs] at h; contradiction
                    | ok child =>
                        rw [hs] at h
                        injection h with h'
                        subst updated
                        cases b with
                        | field name2 =>
                            by_cases hl : name2 = "length"
                            · subst hl; simp [SVal.find]
                            · simp [SVal.find]
                        | «at» j =>
                            have hij : i ≠ j := fun e => hab (by rw [e])
                            by_cases hj : 0 ≤ j ∧ j.toNat < elems.length
                            · have hne : i.toNat ≠ j.toNat := by omega
                              simp [SVal.find, hj, List.getElem_set_ne hne]
                            · simp [SVal.find, hj]
                  next hb => contradiction
                · rename_i entries dflt
                  have finish : ∀ child,
                      (SVal.map (setBy i child entries) dflt).find (b :: q') =
                        (SVal.map entries dflt).find (b :: q') := by
                    intro child
                    cases b with
                    | field name2 => simp [SVal.find]
                    | «at» j =>
                        have hji : j ≠ i := fun e => hab (by rw [e])
                        simp [SVal.find, lookupBy_setBy_ne hji]
                  cases hv : lookupBy i entries with
                  | none =>
                      simp only [SVal.save, hv] at h
                      cases hs : dflt.save rest new with
                      | error e => rw [hs] at h; contradiction
                      | ok child =>
                          rw [hs] at h
                          injection h with h'
                          subst updated
                          exact finish child
                  | some old =>
                      simp only [SVal.save, hv] at h
                      cases hs : old.save rest new with
                      | error e => rw [hs] at h; contradiction
                      | ok child =>
                          rw [hs] at h
                          injection h with h'
                          subst updated
                          exact finish child

/-- Reads compose along `++`: the interpreter's `find_append`. -/
theorem SVal.find_append (v : SVal) (p r : List Seg) :
    v.find (p ++ r) = v.find p >>= fun w => w.find r := by
  induction p generalizing v with
  | nil => simp [SVal.find, bind, Except.bind]
  | cons seg rest ih =>
      cases seg with
      | field name =>
          cases v with
          | prim _ => simp [SVal.find, bind, Except.bind]
          | struct fields =>
              cases hv : lookupBy name fields with
              | none => simp [SVal.find, hv, bind, Except.bind]
              | some c => simp [SVal.find, hv, ih]
          | array elems shadow =>
              by_cases hl : name = "length"
              · subst hl
                cases rest with
                | nil => simp [SVal.find, bind, Except.bind]
                | cons _ _ => simp [SVal.find, bind, Except.bind]
              · simp [SVal.find, bind, Except.bind]
          | map _ _ => simp [SVal.find, bind, Except.bind]
      | «at» i =>
          cases v with
          | prim _ => simp [SVal.find, bind, Except.bind]
          | struct _ => simp [SVal.find, bind, Except.bind]
          | array elems shadow =>
              by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
              · simp [SVal.find, hb, ih]
              · simp [SVal.find, hb, bind, Except.bind]
          | map entries dflt =>
              cases hv : lookupBy i entries with
              | none => simp [SVal.find, hv, ih]
              | some c => simp [SVal.find, hv, ih]

theorem lookupBy_defaultOfFields (name : Name) :
    ∀ fields : List (Name × SVal),
      lookupBy name (SVal.defaultOf.defaultOfFields fields) =
        (lookupBy name fields).map SVal.defaultOf
  | [] => rfl
  | (n, v) :: rest => by
      by_cases h : name = n
      · simp [SVal.defaultOf.defaultOfFields, lookupBy, h]
      · simp [SVal.defaultOf.defaultOfFields, lookupBy, h, lookupBy_defaultOfFields name rest]

/-- **A delete, read through fields**: a primitive member of a deleted value
reads as that primitive's default. -/
theorem SVal.find_defaultOf {c : SVal} {r : List Seg} {l : PrimVal}
    (hr : fieldsOnly r = true) (h : c.find r = .ok (SVal.prim l)) :
    c.defaultOf.find r = .ok (SVal.prim l).defaultOf := by
  induction r generalizing c with
  | nil =>
      simp [SVal.find] at h
      subst h
      cases l <;> rfl
  | cons seg rest ih =>
      cases seg with
      | «at» i => simp [fieldsOnly] at hr
      | field name =>
          have hr' : fieldsOnly rest = true := by simpa [fieldsOnly] using hr
          cases c with
          | prim _ => simp [SVal.find] at h
          | map _ _ => simp [SVal.find] at h
          | struct fields =>
              cases hv : lookupBy name fields with
              | none => simp [SVal.find, hv] at h
              | some c1 =>
                  simp only [SVal.find, hv] at h
                  show (SVal.struct (SVal.defaultOf.defaultOfFields fields)).find
                      (Seg.field name :: rest) = _
                  simp only [SVal.find, lookupBy_defaultOfFields, hv, Option.map_some]
                  exact ih hr' h
          | array elems shadow =>
              by_cases hl : name = "length"
              · subst hl
                cases rest with
                | nil =>
                    simp [SVal.find] at h
                    subst h
                    simp [SVal.defaultOf, SVal.find]
                | cons _ _ => simp [SVal.find] at h
              · simp [SVal.find] at h

/-- The interpreter's reset of a primitive is the theory's `primDefault`. -/
@[simp] theorem SVal.defaultOf_prim (l : PrimVal) :
    (SVal.prim l).defaultOf = SVal.prim (primDefault l) := by
  cases l <;> rfl

/-! ## Theory: the pre-state leaf and the delete family -/

/-- A read of the untouched pre-state is the pre-state at that path. -/
theorem findSt_cur : ∀ (q p : List Seg), q ≠ [] -> findSt (Struct.cur p) q = st (Struct.cur (p ++ q))
  | [], _, h => absurd rfl h
  | [_], _, _ => rfl
  | a :: b :: r, p, _ => by
      show findSt (Struct.cur (p ++ [a])) (b :: r) = _
      rw [findSt_cur (b :: r) (p ++ [a]) (by simp)]
      simp

theorem storeAt_ne_cur (s : Struct) (a : Seg) (w : StValue) (p : List Seg) :
    storeAt s a w ≠ Struct.cur p := by
  intro h
  cases s with
  | mtSt => simp only [storeAt] at h; cases h
  | copyMem _ _ => simp only [storeAt] at h; cases h
  | cur _ => simp only [storeAt] at h; cases h
  | storeSt s0 b v0 =>
      by_cases hb : b = a
      · rw [storeAt, if_pos hb] at h; cases h
      · rw [storeAt, if_neg hb] at h; cases h

/-- A write at a non-empty path is a node, never the pre-state. -/
theorem save_ne_cur (s : Struct) {r : List Seg} (hr : r ≠ []) (v : StValue) (p : List Seg) :
    save s r v ≠ Struct.cur p := by
  match r, hr with
  | [a], _ => exact storeAt_ne_cur s a v p
  | a :: b :: _, _ => exact storeAt_ne_cur s a _ p

theorem delNode_ne_cur (S : Struct) (p : List Seg) : delNode S ≠ Struct.cur p := by
  induction S using Struct.inductionOn with
  | h0 => simp [delNode]
  | h1 s b v ih =>
      cases b with
      | field f => simp [delNode]
      | «at» i => simpa [delNode] using ih
  | h2 _ _ => simp [delNode]
  | h3 _ => simp [delNode]

/-- A primitive read out of a deleted node: the path is all fields, and the
node held a primitive there, now reset. -/
theorem findSt_delNode_prim :
    ∀ (r : List Seg) (S : Struct) (d : PrimVal), r ≠ [] ->
      findSt (delNode S) r = prim d ->
      fieldsOnly r = true ∧ ∃ l, findSt S r = prim l ∧ d = primDefault l
  | [], _, _, h, _ => absurd rfl h
  | [a], S, d, _, h => by
      cases a with
      | «at» i =>
          rw [show findSt (delNode S) [Seg.at i] = selectSt (delNode S) (Seg.at i) from rfl,
            selectStDelNodeIndexStruct] at h
          cases h
      | field f =>
          rw [show findSt (delNode S) [Seg.field f] = selectSt (delNode S) (Seg.field f) from rfl,
            selectStDelNodeRef] at h
          refine ⟨rfl, ?_⟩
          show ∃ l, selectSt S (Seg.field f) = prim l ∧ d = primDefault l
          cases hs : selectSt S (Seg.field f) with
          | prim l => rw [hs] at h; cases h; exact ⟨l, rfl, rfl⟩
          | st _ => rw [hs] at h; cases h
  | a :: b :: r, S, d, _, h => by
      have hstep : findSt (delNode S) (a :: b :: r)
          = findSt (asStruct (selectSt (delNode S) a)) (b :: r) := rfl
      rw [hstep] at h
      cases a with
      | «at» i =>
          rw [selectStDelNodeIndexStruct, asStruct_st, find_mtSt (by simp)] at h
          cases h
      | field f =>
          rw [selectStDelNodeRef] at h
          cases hs : selectSt S (Seg.field f) with
          | prim l =>
              rw [hs] at h
              rw [show asStruct (delValue (prim l)) = Struct.mtSt from rfl, find_mtSt (by simp)] at h
              cases h
          | st T =>
              rw [hs] at h
              obtain ⟨hr, l, hl, hd⟩ := findSt_delNode_prim (b :: r) T d (by simp) h
              refine ⟨by simpa [fieldsOnly] using hr, l, ?_, hd⟩
              show findSt (asStruct (selectSt S (Seg.field f))) (b :: r) = prim l
              rw [hs]; exact hl

/-- A deleted node never reads as the pre-state: the delete dropped every
view in it. -/
theorem findSt_delNode_ne_cur :
    ∀ (r : List Seg) (S : Struct) (p : List Seg), findSt (delNode S) r ≠ st (Struct.cur p)
  | [], S, p, h => by
      cases h' : delNode S with
      | cur q => exact delNode_ne_cur S q h'
      | _ => rw [show findSt (delNode S) [] = st (delNode S) from rfl, h'] at h; cases h
  | [a], S, p, h => by
      cases a with
      | «at» i =>
          rw [show findSt (delNode S) [Seg.at i] = selectSt (delNode S) (Seg.at i) from rfl,
            selectStDelNodeIndexStruct] at h
          cases h
      | field f =>
          rw [show findSt (delNode S) [Seg.field f] = selectSt (delNode S) (Seg.field f) from rfl,
            selectStDelNodeRef] at h
          cases hs : selectSt S (Seg.field f) with
          | prim l => rw [hs] at h; cases h
          | st T =>
              rw [hs] at h
              exact delNode_ne_cur T p (StValue.st.inj h)
  | a :: b :: r, S, p, h => by
      have hstep : findSt (delNode S) (a :: b :: r)
          = findSt (asStruct (selectSt (delNode S) a)) (b :: r) := rfl
      rw [hstep] at h
      cases a with
      | «at» i =>
          rw [selectStDelNodeIndexStruct, asStruct_st, find_mtSt (by simp)] at h
          cases h
      | field f =>
          rw [selectStDelNodeRef] at h
          cases hs : selectSt S (Seg.field f) with
          | prim l =>
              rw [hs] at h
              rw [show asStruct (delValue (prim l)) = Struct.mtSt from rfl, find_mtSt (by simp)] at h
              cases h
          | st T =>
              rw [hs] at h
              exact findSt_delNode_ne_cur (b :: r) T p h

/-! ## Where a read lies against a write -/

theorem diverges_append_left : ∀ (c p q : List Seg),
    diverges (c ++ p) (c ++ q) = diverges p q
  | [], _, _ => rfl
  | a :: c, p, q => by simp [diverges, diverges_append_left c p q]

theorem diverges_cons (a : Seg) (p q : List Seg) :
    diverges (a :: p) (a :: q) = diverges p q := by
  simp [diverges]

/-- The four ways: the same path, off it, below it, above it. -/
theorem path_cases : ∀ (p q : List Seg),
    q = p ∨ diverges p q = true ∨ (∃ t, t ≠ [] ∧ q = p ++ t) ∨ (∃ t, t ≠ [] ∧ p = q ++ t)
  | [], [] => Or.inl rfl
  | [], b :: q => Or.inr (Or.inr (Or.inl ⟨b :: q, by simp, rfl⟩))
  | a :: p, [] => Or.inr (Or.inr (Or.inr ⟨a :: p, by simp, rfl⟩))
  | a :: p, b :: q => by
      by_cases hab : a = b
      · subst hab
        rcases path_cases p q with h | h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩
        · exact Or.inl (by rw [h])
        · exact Or.inr (Or.inl (by simp [diverges, h]))
        · exact Or.inr (Or.inr (Or.inl ⟨t, ht, by rw [h]; rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨t, ht, by rw [h]; rfl⟩))
      · exact Or.inr (Or.inl (by simp [diverges, hab]))

/-! ## The simulation

`Sim X R pre now`: every read of the theory term `X` below the root `R` that
comes out as a *literal* is what the interpreter now reads there, and every one
that comes out as the untouched pre-state (`cur`) is what it read there before.
Anything else — a struct, a deleted member — is no claim, which is what lets a
`delete` be eager on one side and lazy on the other. -/

def Sim (X : Struct) (R : Name) (pre now : List Seg -> Res SVal) : Prop :=
  ∀ r : List Seg,
    (∀ l, findSt X (Seg.field R :: r) = prim l -> now r = .ok (SVal.prim l)) ∧
    (∀ p', findSt X (Seg.field R :: r) = st (Struct.cur p') ->
      p' = Seg.field R :: r ∧ now r = pre r)

theorem sim_start (R : Name) (pre : List Seg -> Res SVal) : Sim (Struct.cur []) R pre pre := by
  intro r
  rw [findSt_cur _ _ (by simp)]
  exact ⟨fun _ h => (by cases h), fun p' h => ⟨(by cases h; rfl), rfl⟩⟩

/-- A read at, below or above a write that is not a literal and not the
pre-state makes no claim. -/
private theorem no_claim {X : Struct} {R : Name} {r : List Seg} {pre now : List Seg -> Res SVal}
    {v : StValue} (h : findSt X (Seg.field R :: r) = v)
    (hp : ∀ l, v ≠ prim l) (hc : ∀ p', v ≠ st (Struct.cur p')) :
    (∀ l, findSt X (Seg.field R :: r) = prim l -> now r = .ok (SVal.prim l)) ∧
    (∀ p', findSt X (Seg.field R :: r) = st (Struct.cur p') ->
      p' = Seg.field R :: r ∧ now r = pre r) :=
  ⟨fun l h' => absurd (h.symm.trans h') (hp l), fun p' h' => absurd (h.symm.trans h') (hc p')⟩

/-- **A write of a literal** preserves the simulation. -/
theorem sim_save {X : Struct} {R : Name} {pre : List Seg -> Res SVal}
    {old upd : SVal} {base rp : List Seg} {v : PrimVal}
    (hsim : Sim X R pre (fun r => old.find (base ++ r)))
    (hs : old.save (base ++ rp) (SVal.prim v) = .ok upd) :
    Sim (save X (Seg.field R :: rp) (prim v)) R pre (fun r => upd.find (base ++ r)) := by
  intro rq
  rcases path_cases rp rq with h | h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩
  · subst h
    refine ⟨fun l hl => ?_, fun p' hp => ?_⟩
    · rw [find_save_same _ (by simp)] at hl
      cases hl
      exact SVal.find_save_same hs
    · rw [find_save_same _ (by simp)] at hp
      cases hp
  · have ht := find_save_frame X (prim v) (Seg.field R :: rp) (Seg.field R :: rq)
      (by rw [diverges_cons]; exact h)
    have hi : upd.find (base ++ rq) = old.find (base ++ rq) :=
      SVal.find_save_frame hs (by rw [diverges_append_left]; exact h)
    simp only [ht, hi]
    exact hsim rq
  · subst h
    refine no_claim (now := fun r => upd.find (base ++ r)) (pre := pre) (v := st Struct.mtSt)
      ?_ (fun l h => by cases h) (fun p' h => by cases h)
    rw [show Seg.field R :: (rp ++ t) = (Seg.field R :: rp) ++ t from rfl,
      find_save_extends _ (by simp) ht, asStruct_prim, find_mtSt ht]
  · subst h
    have hq := find_save_prefix X (Seg.field R :: rq) ht (prim v)
    exact no_claim (now := fun r => upd.find (base ++ r)) (pre := pre) hq
      (fun l h => by cases h) (fun p' h => save_ne_cur _ ht _ p' (StValue.st.inj h))

/-- **A delete** preserves the simulation: the interpreter's lazy reset and
the theory's eager one agree on every literal the theory still claims. -/
theorem sim_delAt {X : Struct} {R : Name} {pre : List Seg -> Res SVal}
    {old upd c : SVal} {base rp : List Seg}
    (hsim : Sim X R pre (fun r => old.find (base ++ r)))
    (hc : old.find (base ++ rp) = .ok c)
    (hs : old.save (base ++ rp) c.defaultOf = .ok upd) :
    Sim (delAt X (Seg.field R :: rp)) R pre (fun r => upd.find (base ++ r)) := by
  intro rq
  rcases path_cases rp rq with h | h | ⟨t, ht, h⟩ | ⟨t, ht, h⟩
  · subst h
    rw [find_delAt_same _ (by simp)]
    cases hX : findSt X (Seg.field R :: rq) with
    | prim l =>
        have hold : old.find (base ++ rq) = .ok (SVal.prim l) := (hsim rq).1 l hX
        rw [hc] at hold
        cases hold
        refine ⟨fun l' hl => ?_, fun p' hp => by cases hp⟩
        cases hl
        show upd.find (base ++ rq) = _
        rw [SVal.find_save_same hs, SVal.defaultOf_prim]
    | st S =>
        exact ⟨fun l hl => (by cases hl),
          fun p' hp => absurd (StValue.st.inj hp) (delNode_ne_cur S p')⟩
  · have ht := find_delAt_frame X (p := Seg.field R :: rp) (q := Seg.field R :: rq)
      (by rw [diverges_cons]; exact h)
    have hi : upd.find (base ++ rq) = old.find (base ++ rq) :=
      SVal.find_save_frame hs (by rw [diverges_append_left]; exact h)
    simp only [ht, hi]
    exact hsim rq
  · subst h
    rw [show Seg.field R :: (rp ++ t) = (Seg.field R :: rp) ++ t from rfl,
      find_delAt_extends _ (by simp) ht]
    cases hX : findSt X (Seg.field R :: rp) with
    | prim l =>
        rw [show asStruct (delValue (prim l)) = Struct.mtSt from rfl, find_mtSt ht]
        exact ⟨fun l h => (by cases h), fun p' h => (by cases h)⟩
    | st S =>
        rw [show asStruct (delValue (st S)) = delNode S from rfl]
        refine ⟨fun d hd => ?_, fun p' hp => absurd hp (findSt_delNode_ne_cur t S p')⟩
        obtain ⟨hf, l, hl, hd'⟩ := findSt_delNode_prim t S d ht hd
        subst hd'
        have hXt : findSt X (Seg.field R :: (rp ++ t)) = prim l := by
          rw [show Seg.field R :: (rp ++ t) = (Seg.field R :: rp) ++ t from rfl,
            find_append _ _ ht, hX, asStruct_st, hl]
        have hold : old.find (base ++ (rp ++ t)) = .ok (SVal.prim l) := (hsim (rp ++ t)).1 l hXt
        simp only [← List.append_assoc, SVal.find_append, hc, bind, Except.bind] at hold
        show upd.find (base ++ (rp ++ t)) = _
        rw [← List.append_assoc, SVal.find_save_extends hs, SVal.find_defaultOf hf hold,
          SVal.defaultOf_prim]
  · subst h
    have hq := find_save_prefix X (Seg.field R :: rq) ht (delValue (findSt X (Seg.field R :: rq ++ t)))
    have hq' : findSt (delAt X (Seg.field R :: rq ++ t)) (Seg.field R :: rq) = _ := hq
    exact no_claim (now := fun r => upd.find (base ++ r)) (pre := pre) hq'
      (fun l h => by cases h) (fun p' h => save_ne_cur _ ht _ p' (StValue.st.inj h))

end Update
end Solidity
