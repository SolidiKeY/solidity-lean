import Solidity.Update
import Solidity.Semantics.Properties

/-!
# Read after write, as facts about one state

`sol_close` (`Close.lean`) applies the updates `sol_symex` leaves in an
arbitrary state, so what it has to know of a write is not a rewrite rule on
`save` terms (mini-solkey's `Ch14_Updates`) but what the state the write
returns reads at each place.  This module is that knowledge, one lemma per
place, in the form the tactic states it.

**Storage** is mini-solkey's four-way comparison of `Ch15_Decide`, between
the path `p` written and a path `q` read at the same root:

* `q` is `p`, or below it (`Prefix p q`): the read is of the value
  written, at what is left of `q` (`after p q`);
* `q` is above `p`: the read is of a subtree the write changed.  Nothing is
  said of it as a whole; a read *of* such a subtree, `a`, is related back to
  the state it came from (`find_findStorage`), so that a later read below
  it (`bob = alice; … bob.age`) lands in one of the other cases;
* `q` is apart from `p` (`Diverge p q`): the read is as before.

A push and a pop are writes of the whole array (`pushOn`, `popOn`), so
these three cases cover them once the array is named.

**Memory** is the same for an address: the address written reads back the
value, every other one reads as before (`Apart`).  A copy between the two
domains is known member by member: a member of a struct copied to memory
reads what the storage struct holds there, a member of one copied back
what the memory object holds (`copyStToM_member`, `copyMem_member`).

Everything here holds of every state; nothing assumes the storage is well
typed.  A write that halts proves nothing and needs nothing, since the box
is the only modality under which `sol_close` names one.
-/

/-- The rewrites `sol_close` closes a goal with (`Close.lean`). -/
register_simp_attr close_rw

/-- The bare box and diamond, which `sol_close` tries after every lemma of
`close_rw`: a `simp` set listed later is consulted later. -/
register_simp_attr close_rw_last

namespace Solidity

open Semantics SemanticsProperties

namespace Close

/-! ## Paths: apart, below -/

/-- Two storage paths part ways: at some position their segments differ.
`alice.age` and `alice.account.balance` do (`age` against `account`);
`alice` and `alice.age` do not — one is a prefix of the other. -/
def Diverge : List Seg → List Seg → Prop
  | a :: p, b :: q => a ≠ b ∨ Diverge p q
  | _, _ => False

/-- `balances[k]` and `balances[j]` part ways when `k ≠ j`, or later on. -/
@[simp] theorem diverge_cons {a b : Seg} {p q : List Seg} :
    Diverge (a :: p) (b :: q) ↔ a ≠ b ∨ Diverge p q := Iff.rfl

/-- `diverge_cons` as `sol_close` uses it, with the disequation both ways
round: a premise `k != j` then discharges the frame of `balances[k]`
against `balances[j]` whichever of the two was written first. -/
theorem diverge_cons' {a b : Seg} {p q : List Seg} :
    Diverge (a :: p) (b :: q) ↔ (¬ a = b ∨ ¬ b = a) ∨ Diverge p q := by
  simp only [diverge_cons, ne_eq]
  exact ⟨fun h => h.elim (fun h => .inl (.inl h)) .inr,
    fun h => h.elim (fun h => .inl (h.elim id (fun h' e => h' e.symm))) .inr⟩

/-- A root does not part ways with anything below it: `alice` against
`alice.age`. -/
@[simp] theorem not_diverge_nil_left {q : List Seg} : ¬ Diverge [] q := id

/-- Nor does a path with its root: `alice.age` against `alice`. -/
@[simp] theorem not_diverge_nil_right {p : List Seg} : ¬ Diverge p [] := by
  cases p <;> exact id

/-- `p` is a prefix of `q`: `alice` of `alice.age`, `alice.age` of itself. -/
def Prefix : List Seg → List Seg → Prop
  | [], _ => True
  | a :: p, b :: q => a = b ∧ Prefix p q
  | _ :: _, [] => False

/-- What is left of `q` below its prefix `p`: `age` of `alice.age` below
`alice`. -/
def after : List Seg → List Seg → List Seg
  | [], q => q
  | _ :: p, _ :: q => after p q
  | _ :: _, [] => []

/-- The root is a prefix of every path below it. -/
theorem prefix_nil {q : List Seg} : Prefix [] q ↔ True := Iff.rfl
/-- `people[i].age` is below `people[j]` when `i = j`. -/
theorem prefix_cons {a b : Seg} {p q : List Seg} :
    Prefix (a :: p) (b :: q) ↔ a = b ∧ Prefix p q := Iff.rfl
/-- `alice.age` is not above `alice`. -/
theorem prefix_cons_nil {a : Seg} {p : List Seg} : Prefix (a :: p) [] ↔ False := Iff.rfl
/-- Below the root, all of `q` is left. -/
theorem after_nil {q : List Seg} : after [] q = q := rfl
/-- `after` drops the common first segment. -/
theorem after_cons {a b : Seg} {p q : List Seg} : after (a :: p) (b :: q) = after p q := rfl

/-- A prefix and what is left below it make up the path. -/
theorem prefix_append : ∀ {p q : List Seg}, Prefix p q → p ++ after p q = q
  | [], _, _ => rfl
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, ⟨rfl, h⟩ => by simp [after, prefix_append h]

/-! ## Storage: the subtree at a path -/

/-- Reading `alice.account.balance` is reading `balance` in the subtree at
`alice.account`. -/
theorem find_append : ∀ (p : List Seg) (v : SVal) (q : List Seg),
    v.find (p ++ q) = v.find p >>= fun w => w.find q
  | [], v, q => by simp [SVal.find, bind, Except.bind]
  | a :: p, v, q => by
    cases v with
    | prim x => cases a <;> rfl
    | struct fields =>
      cases a with
      | «at» i => rfl
      | field n =>
        simp only [List.cons_append, SVal.find]
        split <;> simp [find_append p, bind, Except.bind]
    | array elems shadow fx =>
      cases a with
      | «at» i =>
        simp only [List.cons_append, SVal.find]
        split <;> simp [find_append p, bind, Except.bind]
      | field n =>
        by_cases hn : n = "length"
        · subst hn; simp only [List.cons_append, SVal.find]
          cases fx
          · exact find_append p _ q
          · rfl
        · simp [SVal.find, bind, Except.bind]
    | map entries dflt =>
      cases a with
      | field n => rfl
      | «at» i =>
        simp only [List.cons_append, SVal.find]
        split <;> simp [find_append p, bind, Except.bind]

/-- `find_append` for a root of the storage. -/
theorem findStorage_append (σ : State) (r : Name) (p q : List Seg) :
    σ.findStorage r (p ++ q) = σ.findStorage r p >>= fun w => w.find q := by
  unfold State.findStorage
  split <;> simp [find_append, bind, Except.bind]

/-- **A subtree read out**: once `alice` read as `a`, `a` reads at `age`
what the storage reads at `alice.age`.  This is how a copy `bob = alice;`
passes a read of `bob.age` back to `alice.age`. -/
theorem find_findStorage {σ : State} {r : Name} {p : List Seg} {a : SVal}
    (h : σ.findStorage r p = .ok a) (q : List Seg) :
    a.find q = σ.findStorage r (p ++ q) := by
  rw [findStorage_append, h]; rfl

/-- A tree read at the root is itself: `(alice's tree).find [] = alice's tree`. -/
theorem find_nil (v : SVal) : v.find [] = .ok v := by
  cases v <;> rfl

/-! ## Storage: read after write -/

/-- **Frame, in a tree**: a write leaves every path apart from it as it was.
After `alice.age = 10;` the tree of `alice` reads the same at `account`;
after `values[0] = 7;` the array reads the same at `[1]` and at `length`;
after `balances[1] = 5;` the mapping reads the same at `[2]`. -/
theorem find_save_diverge {new : SVal} :
    ∀ {p q : List Seg} {old upd : SVal}, Diverge p q → old.save p new = .ok upd →
      upd.find q = old.find q
  | [], _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => (not_diverge_nil_right h).elim
  | a :: p, b :: q, old, upd, h, hs => by
    cases old with
    | prim v => cases a <;> simp [SVal.save] at hs
    | struct fields =>
      cases a with
      | «at» i => simp [SVal.save] at hs
      | field n =>
        simp only [SVal.save] at hs
        split at hs
        · rename_i old' hl
          cases hu : old'.save p new with
          | error e => simp [hu, bind, Except.bind] at hs
          | ok u =>
            simp only [hu, bind, Except.bind, Except.ok.injEq] at hs
            subst hs
            cases b with
            | «at» j => simp [SVal.find]
            | field m =>
              by_cases hnm : m = n
              · subst hnm
                have hd : Diverge p q := by simpa using h
                simp [SVal.find, hl, find_save_diverge hd hu]
              · simp [SVal.find, lookupBy_setBy_ne hnm]
        · simp at hs
    | array elems shadow fx =>
      cases a with
      | field n => simp [SVal.save] at hs
      | «at» i =>
        simp only [SVal.save] at hs
        split at hs
        · rename_i hi
          cases hu : ((elems ++ shadow)[i.toNat]'hi.2).save p new with
          | error e => simp [List.get_eq_getElem, hu, bind, Except.bind] at hs
          | ok u =>
            simp only [List.get_eq_getElem, hu, bind, Except.bind, Except.ok.injEq] at hs
            subst hs
            cases b with
            | field m =>
              -- `length` reads the extent, which a write to a slot keeps
              by_cases hm : m = "length"
              · subst hm; cases fx <;> simp [SVal.find]
              · simp [SVal.find]
            | «at» j =>
              by_cases hij : j = i
              · subst hij
                have hd : Diverge p q := by simpa using h
                have hi' : 0 ≤ j ∧ j.toNat < elems.length + shadow.length := by simpa using hi
                simp [SVal.find, List.take_append_drop, find_save_diverge hd hu, hi']
              · by_cases hj : 0 ≤ j ∧ j.toNat < (elems ++ shadow).length
                · have hne : i.toNat ≠ j.toNat := by omega
                  simp only [List.length_append] at hj
                  simp [SVal.find, List.take_append_drop, hj, List.getElem_set_ne hne]
                · simp only [List.length_append] at hj
                  simp [SVal.find, List.take_append_drop, hj]
        · simp at hs
    | map entries dflt =>
      cases a with
      | field n => simp [SVal.save] at hs
      | «at» i =>
        simp only [SVal.save] at hs
        -- the slot written: the entry at `i`, or the default when there is none
        obtain ⟨old', hold, hfind⟩ : ∃ old' : SVal, (old'.save p new >>= fun u =>
            Except.ok (SVal.map (setBy i u entries) dflt)) = Except.ok upd ∧
            (SVal.map entries dflt).find (.at i :: q) = old'.find q := by
          split at hs <;> rename_i hl <;> exact ⟨_, hs, by simp [SVal.find, hl]⟩
        cases hu : old'.save p new with
        | error e => simp [hu, bind, Except.bind] at hold
        | ok u =>
          simp only [hu, bind, Except.bind, Except.ok.injEq] at hold
          subst hold
          cases b with
          | field m => simp [SVal.find]
          | «at» j =>
            by_cases hij : j = i
            · subst hij
              have hd : Diverge p q := by simpa using h
              simp [SVal.find] at hfind ⊢
              rw [hfind, find_save_diverge hd hu]
            · simp [SVal.find, lookupBy_setBy_ne hij]

/-- **Frame, in the storage**: `alice.age = 10;` leaves `bob.age` (another
root) and `alice.account` (a path apart) as they were. -/
theorem findStorage_saveStorage_apart {σ τ : State} {r r' : Name} {p q : List Seg}
    {v : SVal} (h : σ.saveStorage r p v = .ok τ) (hd : r' ≠ r ∨ Diverge p q) :
    τ.findStorage r' q = σ.findStorage r' q := by
  unfold State.saveStorage at h
  split at h
  · rename_i old hl
    cases hu : old.save p v with
    | error e => simp [hu, bind, Except.bind] at h
    | ok u =>
      simp only [hu, bind, Except.bind, Except.ok.injEq] at h
      subst h
      by_cases hr : r' = r
      · subst hr
        have hd : Diverge p q := hd.resolve_left (· rfl)
        simp [State.findStorage, hl, find_save_diverge hd hu]
      · simp [State.findStorage, lookupBy_setBy_ne hr]
  · simp at h

/-- An index into what a path names: in bounds of an array's live elements,
or any key of a mapping; a word or a struct takes none. -/
def idxOk (k : Int) : SVal → Res Unit
  | .array elems _ _ => if 0 ≤ k ∧ k.toNat < elems.length then .ok () else .error .revert
  | .map _ _ => .ok ()
  | .prim _ | .struct _ => .error .stuck

/-- The slot one past an array's end, once the array is named. -/
def pastEnd (rs : Name × List Seg) : SVal → Res (Name × List Seg)
  | .array elems _ _ => .ok (rs.1, rs.2 ++ [.at elems.length])
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- `values[k]` with `k` in bounds. -/
@[simp] theorem idxOk_array (k : Int) (elems shadow : List SVal) (fx : Bool) :
    idxOk k (.array elems shadow fx) =
      if 0 ≤ k ∧ k.toNat < elems.length then .ok () else .error .revert := rfl

/-- `balances[k]`: every key. -/
@[simp] theorem idxOk_map (k : Int) (e : List (Int × SVal)) (d : SVal) :
    idxOk k (.map e d) = .ok () := rfl

@[simp] theorem pastEnd_array (rs : Name × List Seg) (elems shadow : List SVal) (fx : Bool) :
    pastEnd rs (.array elems shadow fx) = .ok (rs.1, rs.2 ++ [.at elems.length]) := rfl

/-- One step down a write: the child written below, before and after. -/
theorem save_cons_find {a : Seg} {p : List Seg} {old new upd : SVal}
    (hs : old.save (a :: p) new = .ok upd) :
    ∃ c u : SVal, c.save p new = .ok u ∧
      ∀ q, old.find (a :: q) = c.find q ∧ upd.find (a :: q) = u.find q := by
  cases old with
  | prim _ => cases a <;> simp [SVal.save] at hs
  | struct fields =>
    cases a with
    | «at» _ => simp [SVal.save] at hs
    | field n =>
      simp only [SVal.save] at hs
      split at hs
      · rename_i o hl
        obtain ⟨u, hu, hs⟩ := Semantics.bind_ok_inv hs
        cases hs
        exact ⟨o, u, hu, fun q => ⟨by simp [SVal.find, hl], by simp [SVal.find]⟩⟩
      · simp at hs
  | array elems shadow fx =>
    cases a with
    | field _ => simp [SVal.save] at hs
    | «at» i =>
      simp only [SVal.save] at hs
      split at hs
      · rename_i hi
        obtain ⟨u, hu, hs⟩ := Semantics.bind_ok_inv hs
        cases hs
        have hi' : 0 ≤ i ∧ i.toNat < elems.length + shadow.length := by simpa using hi
        refine ⟨_, u, hu, fun q => ⟨?_, ?_⟩⟩
        · simp [SVal.find, hi']
        · simp [SVal.find, List.take_append_drop, hi']
      · simp at hs
  | map entries dflt =>
    cases a with
    | field _ => simp [SVal.save] at hs
    | «at» i =>
      simp only [SVal.save] at hs
      split at hs
      · rename_i o hl
        obtain ⟨u, hu, hs⟩ := Semantics.bind_ok_inv hs
        cases hs
        exact ⟨o, u, hu, fun q => ⟨by simp [SVal.find, hl], by simp [SVal.find]⟩⟩
      · rename_i hl
        obtain ⟨u, hu, hs⟩ := Semantics.bind_ok_inv hs
        cases hs
        exact ⟨dflt, u, hu, fun q => ⟨by simp [SVal.find, hl], by simp [SVal.find]⟩⟩

/-- A write below an array or a mapping keeps what an index into it may be:
`values[0] = 7;` leaves `values` as long as it was. -/
theorem idxOk_save_cons {k : Int} {a : Seg} {rest : List Seg} {old new upd : SVal}
    (h : old.save (a :: rest) new = .ok upd) : idxOk k upd = idxOk k old := by
  cases old with
  | prim _ => cases a <;> simp [SVal.save] at h
  | struct fields =>
    cases a with
    | «at» _ => simp [SVal.save] at h
    | field n =>
      simp only [SVal.save] at h
      split at h
      · obtain ⟨u, _, h⟩ := Semantics.bind_ok_inv h; cases h; rfl
      · simp at h
  | array elems shadow fx =>
    cases a with
    | field _ => simp [SVal.save] at h
    | «at» i =>
      simp only [SVal.save] at h
      split at h
      · rename_i hi
        obtain ⟨u, _, h⟩ := Semantics.bind_ok_inv h
        cases h
        have hlen : (((elems ++ shadow).set i.toNat u).take elems.length).length =
            elems.length := by simp
        simp only [idxOk, hlen]
      · simp at h
  | map entries dflt =>
    cases a with
    | field _ => simp [SVal.save] at h
    | «at» i =>
      simp only [SVal.save] at h
      split at h <;> (obtain ⟨u, _, h⟩ := Semantics.bind_ok_inv h; cases h; rfl)

/-- **An index read above or apart from a write** is checked as before:
after `balances[a] = 1;` any key of `balances` is in bounds, and after
`values[0] = 7;` `values` is as long as it was. -/
theorem find_save_idxOk {k : Int} {new : SVal} :
    ∀ {p q : List Seg} {old upd : SVal}, old.save p new = .ok upd → ¬ Prefix p q →
      (upd.find q >>= idxOk k) = (old.find q >>= idxOk k)
  | [], _, _, _, _, hq => (hq trivial).elim
  | _ :: _, [], _, _, hs, _ => by
    simp only [find_nil, bind, Except.bind, idxOk_save_cons hs]
  | a :: p, b :: q, old, upd, hs, hq => by
    by_cases hab : a = b
    · subst hab
      have hq' : ¬ Prefix p q := fun h => hq ⟨rfl, h⟩
      obtain ⟨c, u, hu, hf⟩ := save_cons_find hs
      rw [(hf q).1, (hf q).2]
      exact find_save_idxOk hu hq'
    · rw [find_save_diverge (show Diverge (a :: p) (b :: q) from Or.inl hab) hs]

/-- `find_save_idxOk` at a root of the storage. -/
theorem findStorage_saveStorage_idxOk {σ τ : State} {r r' : Name} {p q : List Seg} {v : SVal}
    (k : Int) (h : σ.saveStorage r p v = .ok τ) (hq : r' ≠ r ∨ ¬ Prefix p q) :
    (τ.findStorage r' q >>= idxOk k) = (σ.findStorage r' q >>= idxOk k) := by
  unfold State.saveStorage at h
  split at h
  · rename_i old hl
    obtain ⟨u, hu, h⟩ := Semantics.bind_ok_inv h
    cases h
    by_cases hr : r' = r
    · subst hr
      simp only [State.findStorage, lookupBy_setBy_self, hl]
      exact find_save_idxOk hu (hq.resolve_left (· rfl))
    · simp [State.findStorage, lookupBy_setBy_ne hr]
  · simp at h

/-- The bounds check reads what the path names, and checks the index there. -/
theorem checkIndex_eq (σ : State) (r : Name) (q : List Seg) (k : Int) :
    σ.checkIndex r q k = σ.findStorage r q >>= idxOk k := by
  unfold State.checkIndex
  cases σ.findStorage r q with
  | error => rfl
  | ok a => cases a <;> rfl

/-- A state reading the storage alike checks alike. -/
theorem checkIndex_of_findStorage {σ τ : State} (h : ∀ r q, τ.findStorage r q = σ.findStorage r q)
    (r : Name) (q : List Seg) (k : Int) : τ.checkIndex r q k = σ.checkIndex r q k := by
  simp only [checkIndex_eq, h]

/-- **A check above or apart from a write** is as before: after
`balances[a] = 1;`, `balances[b]` is checked as before. -/
theorem checkIndex_saveStorage_apart {σ τ : State} {r r' : Name} {p q : List Seg} {v : SVal}
    (k : Int) (h : σ.saveStorage r p v = .ok τ) (hq : r' ≠ r ∨ ¬ Prefix p q) :
    τ.checkIndex r' q k = σ.checkIndex r' q k := by
  simp only [checkIndex_eq]
  exact findStorage_saveStorage_idxOk k h hq

/-- **Below a write**: after `alice = bob;`, `alice.age` reads `age` in the
tree copied from `bob`; after `alice.age = 10;`, `alice.age` reads `10`. -/
theorem findStorage_saveStorage_below {σ τ : State} {r : Name} {p q : List Seg} {v : SVal}
    (h : σ.saveStorage r p v = .ok τ) (hq : Prefix p q) :
    τ.findStorage r q = v.find (after p q) := by
  calc τ.findStorage r q = τ.findStorage r (p ++ after p q) := by rw [prefix_append hq]
    _ = v.find (after p q) := by
      rw [findStorage_append, State.findStorage_saveStorage_same h]; rfl

/-- **A check at or below a write** reads the value written: after
`values = other;`, `values[0]` is checked against `other`'s length. -/
theorem checkIndex_saveStorage_below {σ τ : State} {r : Name} {p q : List Seg} {v : SVal}
    (k : Int) (h : σ.saveStorage r p v = .ok τ) (hq : Prefix p q) :
    τ.checkIndex r q k = v.find (after p q) >>= idxOk k := by
  rw [checkIndex_eq, findStorage_saveStorage_below h hq]

/-- A write fails where the read of its path fails, and the same way:
`persons[5].age = 1;` with no `persons[5]`. -/
theorem save_of_find_error : ∀ {v : SVal} {p : List Seg} {new : SVal} {e : Halt},
    v.find p = .error e → v.save p new = .error e
  | _, [], _, _, h => by simp [find_nil] at h
  | .prim _, a :: _, _, _, h => by cases a <;> simpa [SVal.find, SVal.save] using h
  | .struct fields, .field n :: p, new, e, h => by
    simp only [SVal.find] at h
    simp only [SVal.save]
    split at h
    · rename_i o hl
      (try rw [hl])
      simp [save_of_find_error h, bind, Except.bind]
    · rename_i hl
      (try rw [hl]); exact h
  | .struct _, .at _ :: _, _, _, h => by simpa [SVal.find, SVal.save] using h
  | .array elems shadow _, .at i :: p, new, e, h => by
    simp only [SVal.find] at h
    simp only [SVal.save]
    split at h
    · rename_i hi
      rw [dif_pos hi]
      simp [List.get_eq_getElem] at h
      simp [List.get_eq_getElem, save_of_find_error h, bind, Except.bind]
    · rename_i hi
      rw [dif_neg hi]; exact h
  | .array elems shadow fx, .field n :: p, new, e, h => by
    by_cases hn : n = "length"
    · subst hn
      cases p with
      | nil => cases fx <;> simp_all [SVal.find, SVal.save]
      | cons b p => simpa [SVal.find, SVal.save] using h
    · simpa [SVal.find, SVal.save, hn] using h
  | .map entries dflt, .at i :: p, new, e, h => by
    simp only [SVal.find] at h
    simp only [SVal.save]
    split at h
    · rename_i o hl
      (try rw [hl])
      simp [save_of_find_error h, bind, Except.bind]
    · rename_i hl
      (try rw [hl])
      simp [save_of_find_error h, bind, Except.bind]
  | .map _ _, .field _ :: _, _, _, h => by simpa [SVal.find, SVal.save] using h

/-- **A write, as `sol_close` reads it**: the value there is read, and what is
written laid over it (`SVal.overlay`, which a word replaces): `alice = bob;`
is `alice`'s old tree with `bob`'s members laid over it. -/
theorem writeStorage_eq (σ : State) (r : Name) (p : List Seg) (v : SVal) :
    σ.writeStorage r p v = σ.findStorage r p >>= fun cur => σ.saveStorage r p (cur.overlay v) := by
  unfold State.writeStorage
  split
  · rename_i q
    unfold State.findStorage State.saveStorage
    cases hl : lookupBy r σ.storage with
    | none => rfl
    | some root =>
      simp only
      cases hf : root.find p with
      | error e => simp [save_of_find_error hf, bind, Except.bind]
      | ok cur =>
        have : cur.overlay (.prim q) = .prim q := by cases cur <;> rfl
        simp [this, bind, Except.bind]
  all_goals rfl

/-! ## Storage: reading through a copy

A copy lays the source over the tree there (`SVal.overlay`).  Along members
it is read as the source, laid over what the target held at the same
place: a word read is the source's word. -/

/-- A path of members only: `account.balance`, `tokens.length`. -/
def fieldPath : List Seg → Bool
  | [] => true
  | .field _ :: q => fieldPath q
  | .at _ :: _ => false

@[simp] theorem fieldPath_nil : fieldPath [] = true := rfl
@[simp] theorem fieldPath_field (f : Name) (q : List Seg) :
    fieldPath (.field f :: q) = fieldPath q := rfl
@[simp] theorem fieldPath_at (i : Int) (q : List Seg) : fieldPath (.at i :: q) = false := rfl

/-- What a copy leaves at a member path, given what the source holds there:
the source's value laid over the target's (`layAt_prim`: a word is the
source's word). -/
def layAt : SVal → List Seg → SVal → SVal
  | old, [], v => old.overlay v
  | .struct ofs, .field f :: q, v =>
    match lookupBy f ofs with
    | some o => layAt o q v
    | none => v.strip
  | _, _ :: _, v => v.strip

theorem stripElems_length : ∀ (l : List SVal), (SVal.strip.stripElems l).length = l.length
  | [] => rfl
  | _ :: l => by simp [SVal.strip.stripElems, stripElems_length l]

/-- A word copied is the word: `alice.age` after `alice = bob;` is `bob.age`. -/
@[simp] theorem layAt_prim (old : SVal) (q : List Seg) (p : PrimVal) :
    layAt old q (.prim p) = .prim p := by
  induction q generalizing old with
  | nil => cases old <;> rfl
  | cons s q ih =>
    cases old with
    | struct ofs =>
      cases s with
      | field f =>
        simp only [layAt]
        split
        · exact ih _
        · rfl
      | «at» _ => rfl
    | prim _ => rfl
    | array _ _ _ => rfl
    | map _ _ => rfl

/-- Reading laid-on-fresh-slots values along members: as before, stripped. -/
theorem find_strip_fields : ∀ (v : SVal) (q : List Seg), fieldPath q = true →
    v.strip.find q = v.find q >>= fun w => .ok w.strip
  | v, [], _ => by simp [find_nil, bind, Except.bind]
  | .prim _, .field _ :: _, _ => by simp [SVal.strip, SVal.find, bind, Except.bind]
  | .struct fields, .field f :: q, hq => by
    simp only [fieldPath_field] at hq
    have hl : ∀ fs : List (Name × SVal), lookupBy f (SVal.strip.stripFields fs) =
        (lookupBy f fs).map SVal.strip := by
      intro fs
      induction fs with
      | nil => rfl
      | cons hd tl ih =>
        obtain ⟨n, w⟩ := hd
        simp only [SVal.strip.stripFields, lookupBy]
        split <;> simp_all
    simp only [SVal.strip, SVal.find, hl fields]
    cases lookupBy f fields with
    | none => rfl
    | some w => exact find_strip_fields w q hq
  | .array elems shadow fx, .field f :: q, hq => by
    by_cases hf : f = "length"
    · subst hf
      have hlen : (SVal.strip.stripElems elems).length = elems.length := by
        induction elems with
        | nil => rfl
        | cons _ _ ih => simp [SVal.strip.stripElems, ih]
      simp only [SVal.strip, SVal.find, hlen]
      cases fx; rotate_left
      · rfl
      cases q with
      | nil => simp [find_nil, bind, Except.bind, SVal.strip]
      | cons s q => cases s <;> simp [SVal.find, bind, Except.bind]
    · simp [SVal.strip, SVal.find, hf, bind, Except.bind]
  | .map _ _, .field _ :: _, _ => by simp [SVal.strip, SVal.find, bind, Except.bind]
  | _, .at _ :: _, hq => by simp at hq

/-- **A copy read along members** is the source read, laid over the target
(`SVal.overlay`): after `alice = bob;`, `alice.age` reads `bob.age`
(`layAt_prim`). -/
theorem find_overlay_fields : ∀ (old new : SVal) (q : List Seg), fieldPath q = true →
    (old.overlay new).find q = new.find q >>= fun v => .ok (layAt old q v)
  | old, new, [], _ => by simp [find_nil, bind, Except.bind, layAt]
  | old, new, .field f :: q, hq => by
    simp only [fieldPath_field] at hq
    cases new with
    | prim p => cases old <;> simp [SVal.overlay, SVal.strip, SVal.find, bind, Except.bind]
    | map ne nd => cases old <;> simp [SVal.overlay, SVal.strip, SVal.find, bind, Except.bind]
    | struct nfs =>
      cases old with
      | struct ofs =>
        have hl : ∀ ns : List (Name × SVal), lookupBy f (SVal.overlay.overlayFields ofs ns) =
            (lookupBy f ns).map (fun v => match lookupBy f ofs with
              | some o => o.overlay v
              | none => v.strip) := by
          intro ns
          induction ns with
          | nil => rfl
          | cons hd tl ih =>
            obtain ⟨n, w⟩ := hd
            simp only [SVal.overlay.overlayFields, lookupBy]
            split
            · rename_i hn; subst hn; first | rfl | simp_all
            · exact ih
        simp only [SVal.overlay, SVal.find, hl nfs, layAt]
        cases hn : lookupBy f nfs with
        | none => rfl
        | some w =>
          simp only [Option.map]
          cases ho : lookupBy f ofs with
          | none =>
            simp only
            rw [find_strip_fields w q hq]
          | some o =>
            simp only
            rw [find_overlay_fields o w q hq]
      | prim _ | array _ _ _ | map _ _ =>
        exact (find_strip_fields (.struct nfs) (.field f :: q) (by simpa using hq)).trans rfl
    | array nel nsh nfx =>
      by_cases hf : f = "length"
      · subst hf
        have hlen : ∀ os : List SVal, (SVal.overlay.overlayElems os nel).length = nel.length := by
          intro os
          induction nel generalizing os with
          | nil => cases os <;> rfl
          | cons x xs ih =>
            cases os with
            | nil =>
              simp only [SVal.overlay.overlayElems]
              exact stripElems_length _
            | cons o os => simp [SVal.overlay.overlayElems, ih]
        cases nfx; rotate_left
        · cases old <;> rfl
        cases old with
        | array oel osh ofx =>
          simp only [SVal.overlay, SVal.find, hlen]
          cases q with
          | nil => simp [find_nil, bind, Except.bind, layAt, SVal.strip]
          | cons s q => cases s <;> simp [SVal.find, bind, Except.bind]
        | prim _ | struct _ | map _ _ =>
          exact (find_strip_fields (.array nel nsh false) (.field "length" :: q) (by simpa using hq)).trans
            (by cases q <;> simp [SVal.find, bind, Except.bind, layAt_prim, SVal.strip])
      · cases old <;> simp [SVal.overlay, SVal.strip, SVal.find, hf, bind, Except.bind]
  | _, _, .at _ :: _, hq => by simp at hq


/-- A write changes the storage only: the state an update `{storage :=
save(storage, alice.age, 10)}` builds from `σ` is the one the write returns. -/
theorem saveStorage_restore {σ τ : State} {r : Name} {p : List Seg} {v : SVal}
    (h : σ.saveStorage r p v = .ok τ) : { σ with storage := τ.storage } = τ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := State.saveStorage_frame h
  cases τ; simp_all

/-- The update `{storage := save(storage, alice.age, 10)}` is the write:
the state it builds from `σ` is the one `saveStorage` returns. -/
theorem saveStorage_bind_restore (σ : State) (r : Name) (p : List Seg) (v : SVal) :
    (σ.saveStorage r p v >>= fun τ => Except.ok { σ with storage := τ.storage }) =
      σ.saveStorage r p v := by
  cases h : σ.saveStorage r p v with
  | error _ => rfl
  | ok τ => exact congrArg Except.ok (saveStorage_restore h)

/-- A write leaves the locals alone: `x` reads the same after
`alice.age = 10;`. -/
theorem getEnv_saveStorage {σ τ : State} {r : Name} {p : List Seg} {v : SVal}
    (h : σ.saveStorage r p v = .ok τ) (x : Var) : τ.getEnv x = σ.getEnv x := by
  simp [State.getEnv, (State.saveStorage_frame h).2.2.1]

/-- A write leaves the heap alone: `m.age` reads the same after
`alice.age = 10;`. -/
theorem readAddr_saveStorage {σ τ : State} {r : Name} {p : List Seg} {v : SVal}
    (h : σ.saveStorage r p v = .ok τ) (a : Addr) : readAddr τ a = readAddr σ a := by
  have hh := (State.saveStorage_frame h).1
  cases a <;> simp [readAddr, State.getObj, hh]

/-! ## Push and pop: a write of the whole array -/

/-- What `values.push(5)` does to the array `values` reads as, once it is
named: append, and write the result back. -/
def pushOn (σ : State) (E : Ty) (r : Name) (segs : List Seg) (val : SVal → Res SVal) :
    SVal → Res State
  | .array elems shadow fx => val (pushSlot E shadow).1 >>= fun v =>
      σ.saveStorage r segs (.array (elems ++ [v]) (pushSlot E shadow).2 fx)
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- What `values.pop()` does to the array, once it is named. -/
def popOn (σ : State) (keep : Bool) (r : Name) (segs : List Seg) : SVal → Res State
  | .array elems shadow fx =>
    match elems.reverse with
    | [] => .error .revert
    | last :: restRev =>
      σ.saveStorage r segs
        (.array restRev.reverse ((if keep then last else last.defaultOf) :: shadow) fx)
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- The length of an array, once it is named. -/
def arrLen : SVal → Res Value
  | .array elems _ _ => .ok (.int elems.length)
  | .prim _ | .struct _ | .map _ _ => .error .stuck

/-- `values.push(5)` reads `values`, then writes it back one longer. -/
theorem pushAt_eq (σ : State) (E : Ty) (r : Name) (segs : List Seg) (val : SVal → Res SVal) :
    pushAt σ E r segs val = σ.findStorage r segs >>= pushOn σ E r segs val := by
  unfold pushAt
  cases σ.findStorage r segs with
  | error _ => rfl
  | ok a => cases a <;> rfl

/-- `values.pop()` reads `values`, then writes it back one shorter. -/
theorem popAt_eq (σ : State) (keep : Bool) (r : Name) (segs : List Seg) :
    popAt σ keep r segs = σ.findStorage r segs >>= popOn σ keep r segs := by
  unfold popAt
  cases σ.findStorage r segs with
  | error _ => rfl
  | ok a => cases a <;> rfl

/-- `values.length` reads `values`, then counts. -/
theorem arrayLen_eq (σ : State) (r : Name) (segs : List Seg) :
    arrayLen σ r segs = σ.findStorage r segs >>= arrLen := by
  unfold arrayLen
  cases σ.findStorage r segs with
  | error _ => rfl
  | ok a => cases a <;> rfl

/-- A push onto a named array appends. -/
theorem pushOn_array (σ : State) (E : Ty) (r : Name) (segs : List Seg)
    (val : SVal → Res SVal) (elems : List SVal) (shadow : List SVal) (fx : Bool) :
    pushOn σ E r segs val (.array elems shadow fx) = val (pushSlot E shadow).1 >>= fun v =>
      σ.saveStorage r segs (.array (elems ++ [v]) (pushSlot E shadow).2 fx) := rfl

/-- A pop after a push takes the pushed element off:
`values.push(6); values.pop();` leaves `values` as it was, but for the
recycled slot. -/
theorem popOn_push (σ : State) (r : Name) (segs : List Seg) (elems : List SVal)
    (x : SVal) (shadow : List SVal) (fx : Bool) :
    popOn σ false r segs (.array (elems ++ [x]) shadow fx) =
      σ.saveStorage r segs (.array elems (x.defaultOf :: shadow) fx) := by
  simp [popOn]

/-- An array of mappings popped after a push keeps the pushed element in the
recycled slot, as it is. -/
theorem popOn_push_keep (σ : State) (r : Name) (segs : List Seg) (elems : List SVal)
    (x : SVal) (shadow : List SVal) (fx : Bool) :
    popOn σ true r segs (.array (elems ++ [x]) shadow fx) =
      σ.saveStorage r segs (.array elems (x :: shadow) fx) := by
  simp [popOn]

/-- An array is as long as its elements. -/
theorem arrLen_array (elems shadow : List SVal) (fx : Bool) :
    arrLen (.array elems shadow fx) = .ok (.int elems.length) := rfl

/-- A length was read off an array: `values.length == n` says `values` is
an array of `n` elements. -/
theorem arrLen_eq_ok {a : SVal} {v : Value} :
    arrLen a = .ok v ↔ ∃ elems shadow fx, a = .array elems shadow fx ∧ v = .int elems.length := by
  cases a <;> simp [arrLen, eq_comm]

/-- The element a push appended: after `values.push(5)` on an array of `n`
elements, `values[n]` reads `5`. -/
theorem find_push_last {elems : List SVal} {x : SVal} {shadow : List SVal} {fx : Bool} {i : Int}
    (hi : i = elems.length) (q : List Seg) :
    (SVal.array (elems ++ [x]) shadow fx).find (.at i :: q) = x.find q := by
  subst hi
  simp [SVal.find]

/-! ## Memory: read after write -/

/-- Two memory addresses a write at the first leaves the second alone at:
`m.age` and `n.age` when `m` and `n` are different objects, `m.age` and
`m.account`; an element and a member never meet, since an object is a
struct or an array, not both. -/
def Apart : Addr → Addr → Prop
  | .memoryField id f, .memoryField id' f' => ¬ id' = id ∨ ¬ f' = f
  | .memoryIndex id i, .memoryIndex id' i' => ¬ id' = id ∨ ¬ i' = i
  | .memoryField .., .memoryIndex .. | .memoryIndex .., .memoryField .. => True

/-- `m.age` and `n.balance`. -/
theorem apart_field {id id' : Nat} {f f' : Name} :
    Apart (.memoryField id f) (.memoryField id' f') ↔ ¬ id' = id ∨ ¬ f' = f := Iff.rfl
/-- `xs[i]` and `ys[j]`. -/
theorem apart_index {id id' : Nat} {i i' : Int} :
    Apart (.memoryIndex id i) (.memoryIndex id' i') ↔ ¬ id' = id ∨ ¬ i' = i := Iff.rfl
/-- `m.age` and `xs[0]`. -/
theorem apart_field_index {id id' : Nat} {f : Name} {i : Int} :
    Apart (.memoryField id f) (.memoryIndex id' i) ↔ True := Iff.rfl
/-- `xs[0]` and `m.age`. -/
theorem apart_index_field {id id' : Nat} {f : Name} {i : Int} :
    Apart (.memoryIndex id i) (.memoryField id' f) ↔ True := Iff.rfl

/-- The value at a memory address: what `read(memory, m.age)` is. -/
def readVal (σ : State) (a : Addr) : Res Value := readAddr σ a >>= MVal.asValue

/-- `m.age = 5;` writes `5` at `m.age`. -/
theorem readAddr_writeAddr_same {σ τ : State} {mv : MVal} {a : Addr}
    (h : writeAddr σ mv a = .ok τ) : readAddr τ a = .ok mv := by
  cases a with
  | memoryField id f =>
    simp only [writeAddr, memWriteField, bind, Except.bind] at h
    cases hg : σ.getObj id with
    | error e => simp [hg] at h
    | ok obj =>
      cases obj with
      | array _ => simp [hg] at h
      | struct fields =>
        simp only [hg, Except.ok.injEq] at h
        subst h
        simp [readAddr, State.getObj, State.setObj, bind, Except.bind, pure, Except.pure]
  | memoryIndex id i =>
    simp only [writeAddr, memWriteIndex, bind, Except.bind] at h
    cases hg : σ.getObj id with
    | error e => simp [hg] at h
    | ok obj =>
      cases obj with
      | struct _ => simp [hg] at h
      | array elems =>
        simp only [hg] at h
        split at h
        · rename_i hi
          simp only [Except.ok.injEq] at h
          subst h
          simp [readAddr, State.getObj, State.setObj, bind, Except.bind, pure, Except.pure, hi]
        · simp at h

/-- The heap a memory write leaves: the object written, changed at one place. -/
theorem writeAddr_setObj {σ τ : State} {mv : MVal} {a : Addr} (h : writeAddr σ mv a = .ok τ) :
    ∃ id obj, τ = σ.setObj id obj ∧
      (∀ a', Apart a a' → readAddr τ a' = readAddr σ a') := by
  cases a with
  | memoryField id f =>
    simp only [writeAddr, memWriteField, bind, Except.bind] at h
    cases hg : σ.getObj id with
    | error e => simp [hg] at h
    | ok obj =>
      cases obj with
      | array _ => simp [hg] at h
      | struct fields =>
        simp only [hg, Except.ok.injEq] at h
        subst h
        refine ⟨id, _, rfl, fun a' ha => ?_⟩
        cases a' with
        | memoryField id' f' =>
          by_cases hid : id' = id
          · subst hid
            have hf : f' ≠ f := by simpa [Apart] using ha
            simp [readAddr, State.getObj, State.setObj, bind, Except.bind] at hg ⊢
            simp [hg, lookupBy_setBy_ne hf]
          · simp [readAddr, State.getObj, State.setObj, lookupBy_setBy_ne hid]
        | memoryIndex id' i' =>
          by_cases hid : id' = id
          · subst hid
            simp [readAddr, State.getObj, State.setObj, bind, Except.bind] at hg ⊢
            simp [hg]
          · simp [readAddr, State.getObj, State.setObj, lookupBy_setBy_ne hid]
  | memoryIndex id i =>
    simp only [writeAddr, memWriteIndex, bind, Except.bind] at h
    cases hg : σ.getObj id with
    | error e => simp [hg] at h
    | ok obj =>
      cases obj with
      | struct _ => simp [hg] at h
      | array elems =>
        simp only [hg] at h
        split at h
        · rename_i hi
          simp only [Except.ok.injEq] at h
          subst h
          refine ⟨id, _, rfl, fun a' ha => ?_⟩
          cases a' with
          | memoryIndex id' i' =>
            by_cases hid : id' = id
            · subst hid
              have hii : i' ≠ i := by simpa [Apart] using ha
              simp [readAddr, State.getObj, State.setObj, bind, Except.bind] at hg ⊢
              by_cases hb : 0 ≤ i' ∧ i'.toNat < elems.length
              · have hne : i.toNat ≠ i'.toNat := by omega
                simp [hg, hb, List.getElem_set_ne hne]
              · simp [hg, hb]
            · simp [readAddr, State.getObj, State.setObj, lookupBy_setBy_ne hid]
          | memoryField id' f' =>
            by_cases hid : id' = id
            · subst hid
              simp [readAddr, State.getObj, State.setObj, bind, Except.bind] at hg ⊢
              simp [hg]
            · simp [readAddr, State.getObj, State.setObj, lookupBy_setBy_ne hid]
        · simp at h

/-- The update `{memory := write(memory, m.age, 5)}` is the write: the state
it builds from `σ` is the one `writeAddr` returns. -/
theorem writeAddr_bind_restore (σ : State) (mv : MVal) (a : Addr) :
    (writeAddr σ mv a >>= fun τ => Except.ok { σ with heap := τ.heap, nextId := τ.nextId }) =
      writeAddr σ mv a := by
  cases h : writeAddr σ mv a with
  | error _ => rfl
  | ok τ =>
    obtain ⟨id, obj, rfl, _⟩ := writeAddr_setObj h
    rfl

/-- A memory write leaves the storage alone: `alice.age` reads the same
after `m.age = 5;`. -/
theorem findStorage_setObj (σ : State) (id : Nat) (obj : MObj) (r : Name) (q : List Seg) :
    (σ.setObj id obj).findStorage r q = σ.findStorage r q := rfl

/-- Nor does it touch the locals. -/
theorem getEnv_setObj (σ : State) (id : Nat) (obj : MObj) (x : Var) :
    (σ.setObj id obj).getEnv x = σ.getEnv x := rfl

/-! ## Memory: reads through a changed state

A state built by an update is a structure literal over the states the
update read: `{ τ with storage := τ'.storage }` for a storage write,
`{ τ with heap := μ.heap, nextId := μ.nextId }` for a memory one.  Each read
depends on one component, so it passes to the state that component came
from. -/

/-- `alice.age` in a state whose storage is `τ`'s reads as in `τ`. -/
theorem findStorage_mk (τ : State) (h : List (Nat × MObj)) (n : Nat)
    (e : List (Var × Binding)) (nt : List (Int × Int)) (b : Int) (tx : TxEnv) (r : Name) (q : List Seg) :
    (State.mk τ.storage h n e nt b tx).findStorage r q = τ.findStorage r q := rfl

/-- A bounds check in a state whose storage is `τ`'s checks as in `τ`. -/
theorem checkIndex_mk (τ : State) (h : List (Nat × MObj)) (n : Nat)
    (e : List (Var × Binding)) (nt : List (Int × Int)) (b : Int) (tx : TxEnv) (r : Name) (q : List Seg)
    (k : Int) : (State.mk τ.storage h n e nt b tx).checkIndex r q k = τ.checkIndex r q k := rfl

/-- `x` in a state whose locals are `τ`'s reads as in `τ`. -/
theorem getEnv_mk (τ : State) (s : List (Name × SVal)) (h : List (Nat × MObj)) (n : Nat)
    (nt : List (Int × Int)) (b : Int) (tx : TxEnv) (x : Var) :
    (State.mk s h n τ.env nt b tx).getEnv x = τ.getEnv x := rfl

/-- `m.age` in a state whose heap is `τ`'s reads as in `τ`. -/
theorem readAddr_mk (τ : State) (s : List (Name × SVal)) (n : Nat)
    (e : List (Var × Binding)) (nt : List (Int × Int)) (b : Int) (tx : TxEnv) (a : Addr) :
    readAddr (State.mk s τ.heap n e nt b tx) a = readAddr τ a := by
  cases a <;> rfl

/-- `readAddr_mk` for a value read. -/
theorem readVal_mk (τ : State) (s : List (Name × SVal)) (n : Nat)
    (e : List (Var × Binding)) (nt : List (Int × Int)) (b : Int) (tx : TxEnv) (a : Addr) :
    readVal (State.mk s τ.heap n e nt b tx) a = readVal τ a := by
  simp only [readVal, readAddr_mk]

/-- Binding a local does not touch the heap. -/
theorem readAddr_setEnv (σ : State) (x : Var) (bd : Binding) (a : Addr) :
    readAddr (σ.setEnv x bd) a = readAddr σ a := by
  cases a <;> rfl

/-- `readAddr_setEnv` for a value read. -/
theorem readVal_setEnv (σ : State) (x : Var) (bd : Binding) (a : Addr) :
    readVal (σ.setEnv x bd) a = readVal σ a := by
  simp only [readVal, readAddr_setEnv]

/-! ## Copies between storage and memory -/

/-- A copy into memory keeps each primitive: the copy of `alice.age` is
`alice.age`, and a nested struct, which becomes a reference, reads as no
value on either side. -/
theorem copyStToM_asValue {σ τ : State} {v : SVal} {mv : MVal}
    (h : copyStToM σ v = .ok (τ, mv)) : mv.asValue = v.asValue := by
  cases v with
  | prim p =>
    cases p <;> simp [copyStToM] at h <;> obtain ⟨rfl, rfl⟩ := h <;> rfl
  | map _ _ => simp [copyStToM] at h
  | struct fields =>
    rw [copyStToM] at h
    cases hc : copyStFields σ fields with
    | error e => simp [hc, bind, Except.bind] at h
    | ok r =>
      simp only [hc, bind, Except.bind, State.alloc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      rfl
  | array elems shadow fx =>
    rw [copyStToM] at h
    cases hc : copyStElems σ elems with
    | error e => simp [hc, bind, Except.bind] at h
    | ok r =>
      simp only [hc, bind, Except.bind, State.alloc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      rfl

/-- The members a struct copy into memory holds: each the copy of the
storage member of the same name. -/
theorem copyStFields_lookup {σ τ : State} :
    ∀ {fields : List (Name × SVal)} {mfields : List (Name × MVal)},
      copyStFields σ fields = .ok (τ, mfields) → ∀ f,
        (match lookupBy f mfields with | some mv => mv.asValue | none => .error .stuck) =
          (match lookupBy f fields with | some v => v.asValue | none => .error .stuck)
  | [], mfields, h, f => by
    simp [copyStFields] at h
    obtain ⟨_, rfl⟩ := h
    rfl
  | (n, v) :: rest, mfields, h, f => by
    rw [copyStFields] at h
    cases h1 : copyStToM σ v with
    | error e => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨σ₁, mv⟩ := p
      cases h2 : copyStFields σ₁ rest with
      | error e => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨σ₂, mrest⟩ := q
        simp only [h1, h2, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        by_cases hf : f = n
        · subst hf; simp [lookupBy, copyStToM_asValue h1]
        · simp only [lookupBy, hf, if_false]
          exact copyStFields_lookup h2 f

/-- **A member of a struct copied into memory**: after
`Person memory m = alice;`, `m.age` reads what `alice.age` held. -/
theorem copyStToM_member {σ τ : State} {v : SVal} {id : Nat} {f : Name}
    (h : copyStToM σ v = .ok (τ, .ref id)) (hf : f ≠ "length") :
    readVal τ (.memoryField id f) = v.find [.field f] >>= SVal.asValue := by
  cases v with
  | prim p => cases p <;> simp [copyStToM] at h
  | map _ _ => simp [copyStToM] at h
  | struct fields =>
    rw [copyStToM] at h
    cases hc : copyStFields σ fields with
    | error e => simp [hc, bind, Except.bind] at h
    | ok r =>
      obtain ⟨σ₁, mfields⟩ := r
      simp only [hc, bind, Except.bind, State.alloc, Except.ok.injEq, Prod.mk.injEq,
        MVal.ref.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := copyStFields_lookup hc f
      simp only [readVal, readAddr, State.getObj, lookupBy_setBy_self, SVal.find, bind,
        Except.bind]
      revert this
      cases lookupBy f mfields <;> cases lookupBy f fields <;> simp [pure, Except.pure]
  | array elems shadow fx =>
    rw [copyStToM] at h
    cases hc : copyStElems σ elems with
    | error e => simp [hc, bind, Except.bind] at h
    | ok r =>
      obtain ⟨σ₁, melems⟩ := r
      simp only [hc, bind, Except.bind, State.alloc, Except.ok.injEq, Prod.mk.injEq,
        MVal.ref.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [readVal, readAddr, State.getObj, lookupBy_setBy_self, SVal.find, bind, Except.bind]

/-- A copy into memory allocates, and changes nothing but the heap. -/
theorem copyStToM_frame' {σ τ : State} {v : SVal} {mv : MVal}
    (h : copyStToM σ v = .ok (τ, mv)) :
    (∀ r q, τ.findStorage r q = σ.findStorage r q) ∧ (∀ x, τ.getEnv x = σ.getEnv x) := by
  obtain ⟨hs, he, _, _⟩ := copyStToM_frame σ v τ mv h
  exact ⟨fun r q => by simp [State.findStorage, hs], fun x => by simp [State.getEnv, he]⟩

/-- A copy out of memory of a primitive: the primitive. -/
theorem copyMToSt_prim (σ : State) (rem : List Nat) (p : PrimVal) :
    copyMToSt σ rem (.prim p) = .ok (.prim p) := by
  cases p <;> rw [copyMToSt.eq_def]

/-- The members a struct copy out of memory holds. -/
theorem copyMFields_lookup {σ : State} {rem : List Nat} :
    ∀ {fields : List (Name × MVal)} {sfields : List (Name × SVal)},
      copyMFields σ rem fields = .ok sfields → ∀ f,
        (match lookupBy f sfields with | some v => .ok v | none => .error .stuck) =
          (match lookupBy f fields with
            | some mv => copyMToSt σ rem mv | none => (.error .stuck : Res SVal))
  | [], sfields, h, f => by
    rw [copyMFields] at h
    simp only [Except.ok.injEq] at h
    subst h; rfl
  | (n, mv) :: rest, sfields, h, f => by
    rw [copyMFields] at h
    cases h1 : copyMToSt σ rem mv with
    | error e => simp [h1, bind, Except.bind] at h
    | ok v =>
      cases h2 : copyMFields σ rem rest with
      | error e => simp [h1, h2, bind, Except.bind] at h
      | ok srest =>
        simp only [h1, h2, bind, Except.bind, Except.ok.injEq] at h
        subst h
        by_cases hf : f = n
        · subst hf; simp [lookupBy, h1]
        · simp only [lookupBy, hf, if_false]
          exact copyMFields_lookup h2 f

/-- What a member of a memory object copies to, as a storage value: a
primitive itself, a reference the object it points to. -/
def copyLeaf (σ : State) (id : Nat) (mv : MVal) : Res SVal :=
  copyMToSt σ ((σ.heap.map Prod.fst).erase id) mv

/-- A primitive member copies as itself. -/
theorem copyLeaf_prim (σ : State) (id : Nat) (p : PrimVal) :
    copyLeaf σ id (.prim p) = .ok (.prim p) := copyMToSt_prim σ _ p

/-- **A member of a memory struct copied to storage**: after
`alice = m;`, `alice.age` holds what `m.age` held. -/
theorem copyMem_member {σ : State} {id : Nat} {v : SVal} {f : Name}
    (h : copyMem σ (.ref id) = .ok v) (hf : f ≠ "length") :
    v.find [.field f] = readAddr σ (.memoryField id f) >>= copyLeaf σ id := by
  unfold copyMem at h
  rw [copyMToSt.eq_def] at h
  simp only at h
  split at h
  · rename_i hmem
    cases hg : σ.getObj id with
    | error e => simp [hg] at h
    | ok obj =>
      cases obj with
      | struct fields =>
        cases hc : copyMFields σ ((σ.heap.map Prod.fst).erase id) fields with
        | error e => simp [hg, hc, bind, Except.bind] at h
        | ok sfields =>
          simp only [hg, hc, bind, Except.bind, Except.ok.injEq] at h
          subst h
          have := copyMFields_lookup hc f
          simp only [readAddr, hg, SVal.find, copyLeaf, bind, Except.bind]
          revert this
          cases lookupBy f sfields <;> cases lookupBy f fields <;> simp [pure, Except.pure]
      | array elems =>
        cases hc : copyMElems σ ((σ.heap.map Prod.fst).erase id) elems with
        | error e => simp [hg, hc, bind, Except.bind] at h
        | ok selems =>
          simp only [hg, hc, bind, Except.bind, Except.ok.injEq] at h
          subst h
          simp [readAddr, hg, SVal.find, bind, Except.bind]
  · simp at h

/-- `allocDefault` is a copy of the type's default into memory. -/
theorem allocDefault_copy {σ τ : State} {R : RefTy} {id : Nat}
    (h : allocDefault σ R = .ok (τ, id)) : copyStToM σ (defaultForRef R) = .ok (τ, .ref id) := by
  unfold allocDefault at h
  split at h <;> simp_all

/-! ## `transfer` -/

/-- A transfer books a payment and touches nothing a formula reads: the
storage, the locals and the heap read the same after `to.transfer(5);`. -/
theorem transferAt_frame {σ τ : State} {addr amt : Int} (h : transferAt σ addr amt = .ok τ) :
    (∀ r q, τ.findStorage r q = σ.findStorage r q) ∧ (∀ x, τ.getEnv x = σ.getEnv x) ∧
      (∀ a, readAddr τ a = readAddr σ a) := by
  unfold transferAt at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [Except.ok.injEq] at h
      subst h
      refine ⟨fun _ _ => rfl, fun _ => rfl, fun a => ?_⟩
      cases a <;> rfl

end Close

end Solidity
