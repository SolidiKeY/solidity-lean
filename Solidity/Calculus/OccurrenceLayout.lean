import Solidity.Calculus.FlattenReads
import Solidity.Calculus.ReadFree

/-!
# Fresh dependent-read layouts

An occurrence's path is read-free and uses only earlier atoms; its result
gets the next fresh position. These checked conditions let every actual
storage fill the occurrence atoms without changing the source inputs.
Inactive paths retain failure and impose no storage read.
-/

namespace Solidity.Decide

open Semantics ReadRealization

variable {C : Contract}

/-- A path's executable query retains its declaration proof. -/
def ReadOccurrence.location? (r : ReadOccurrence C) (h : ReadFree r.path.toLTm)
    (g : State C []) (ν : AEnv) : Option {q : SRef C (.prim r.prim) // q.Declared} :=
  (h.query.query g ν).runStorage (Storage.init C)

theorem ReadOccurrence.location?_eq (r : ReadOccurrence C) (h : ReadFree r.path.toLTm)
    (g : State C []) (ν : AEnv) :
    (r.location? h g ν).map Subtype.val = r.path.eval g ν := by
  exact (h.query.query_sound g ν (Storage.init C)).trans
    ((h.eval_storage g ν (Storage.init C)).trans (SPath.eval_toLTm g ν r.path))

/-- Read a successful occurrence in the actual storage. A failed path gets
a typed default only in its unused atom; its term guard still fails. -/
def ReadOccurrence.value (r : ReadOccurrence C) (h : ReadFree r.path.toLTm)
    (g : State C []) (ν : AEnv) : r.prim.Denote :=
  match r.location? h g ν with
  | none => PrimTy.dflt r.prim
  | some q => (⟨r.prim, q.val, q.property⟩ : Ref C).read g.storage

theorem ReadOccurrence.value_eq (r : ReadOccurrence C) (h : ReadFree r.path.toLTm)
    (g : State C []) (ν : AEnv) (q : SRef C (.prim r.prim))
    (hq : r.path.eval g ν = some q) : r.value h g ν = g.storage.obs.word (.ref q) := by
  have he := (r.location?_eq h g ν).trans hq
  obtain ⟨q', hx, rfl⟩ := Option.map_eq_some_iff.mp he
  simpa only [value, hx] using (Ref.obs_read (⟨r.prim, q'.val, q'.property⟩ : Ref C) g.storage).symm

theorem ReadOccurrence.path_storage (r : ReadOccurrence C) (h : ReadFree r.path.toLTm)
    (g : State C []) (ν : AEnv) (st : Storage C) :
    r.path.eval { g with storage := st } ν = r.path.eval g ν := by
  simpa only [SPath.eval_toLTm] using h.eval_storage g ν st

/-- Every key depends only on the input atoms and earlier results. -/
inductive OccurrenceLayout : List (ReadOccurrence C) → Nat → Type where
  | nil (start : Nat) : OccurrenceLayout [] start
  | cons {r : ReadOccurrence C} {rs : List (ReadOccurrence C)} {start : Nat}
      (slot : r.slot = start) (bound : r.path.toLTm.atomBound ≤ start)
      (readFree : ReadFree r.path.toLTm) (tail : OccurrenceLayout rs (start + 1)) :
      OccurrenceLayout (r :: rs) start

def occurrenceLayout? : (fuel : Nat) → (rs : List (ReadOccurrence C)) →
    (start : Nat) → Option (OccurrenceLayout rs start)
  | _, [], start => some (.nil start)
  | 0, _ :: _, _ => none
  | fuel + 1, r :: rs, start => do
    if hs : r.slot = start then
      if hb : r.path.toLTm.atomBound ≤ start then
        return .cons hs hb (← readFree? r.path.toLTm) (← occurrenceLayout? fuel rs (start + 1))
      else none
    else none

namespace OccurrenceLayout

theorem readFree_mem {rs : List (ReadOccurrence C)} {start : Nat}
    (h : OccurrenceLayout rs start) (r : ReadOccurrence C) (hm : r ∈ rs) :
    Nonempty (ReadFree r.path.toLTm) := by
  induction h with
  | nil => cases hm
  | cons _ _ hr _ ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨hr⟩
    · exact ih hm

/-- Materialize only active occurrences. Failed paths contribute no
location, while repeated successful locations remain separate entries. -/
def entries (g : State C []) (ν : AEnv) : {rs : List (ReadOccurrence C)} → {start : Nat} →
    OccurrenceLayout rs start → Assignment C
  | _, _, .nil _ => []
  | _, _, .cons (r := r) _ _ h tail =>
    match r.location? h g ν with
    | none => tail.entries g ν
    | some q => ⟨⟨r.prim, q.val, q.property⟩, ν.get r.prim r.slot⟩ :: tail.entries g ν

theorem entries_contains (g : State C []) (ν : AEnv) {rs : List (ReadOccurrence C)} {start : Nat}
    (h : OccurrenceLayout rs start) (r : ReadOccurrence C) (hm : r ∈ rs)
    (q : SRef C (.prim r.prim)) (hq : r.path.eval g ν = some q) :
    ⟨⟨r.prim, q, r.guard.declared g ν q hq⟩, ν.get r.prim r.slot⟩ ∈ h.entries g ν := by
  induction h with
  | nil => cases hm
  | @cons x xs start hs hb hr tail ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · obtain ⟨q', hx, he⟩ := Option.map_eq_some_iff.mp ((r.location?_eq hr g ν).trans hq)
      subst q
      simpa only [entries, hx] using List.mem_cons_self
        (a := (⟨⟨r.prim, q', q'.property⟩, ν.get r.prim r.slot⟩ : (r : Ref C) × r.Value))
        (l := tail.entries g ν)
    · cases hx : x.location? hr g ν with
      | none => simpa only [entries, hx] using ih hm
      | some a =>
        simpa only [entries, hx] using List.mem_cons_of_mem
          (⟨⟨x.prim, a.val, a.property⟩, ν.get x.prim x.slot⟩ : (r : Ref C) × r.Value) (ih hm)

theorem entries_read (g : State C []) (ν : AEnv) {rs : List (ReadOccurrence C)} {start : Nat}
    (h : OccurrenceLayout rs start) (hi : ReadOccurrence.All g ν rs)
    (e : (r : Ref C) × r.Value) (he : e ∈ h.entries g ν) : e.1.read g.storage = e.2 := by
  induction h with
  | nil => cases he
  | @cons r rs start hs hb hr tail ih =>
    cases hx : r.location? hr g ν with
    | none => exact ih (fun x hm => hi x (List.mem_cons_of_mem _ hm)) (by simpa only [entries, hx] using he)
    | some q =>
      rcases List.mem_cons.mp (show e ∈ _ :: tail.entries g ν by simpa only [entries, hx] using he) with he | he
      · subst e
        exact ((hi r List.mem_cons_self q.val ((r.location?_eq hr g ν).symm.trans
          (congrArg (Option.map Subtype.val) hx))).trans
          (Ref.obs_read (⟨r.prim, q.val, q.property⟩ : Ref C) g.storage)).symm
      · exact ih (fun x hm => hi x (List.mem_cons_of_mem _ hm)) he

theorem entries_consistent (g : State C []) (ν : AEnv) {rs : List (ReadOccurrence C)} {start : Nat}
    (h : OccurrenceLayout rs start) (hi : ReadOccurrence.All g ν rs) :
    (h.entries g ν).Consistent :=
  fun r v w hv hw => (h.entries_read g ν hi ⟨r, v⟩ hv).symm.trans (h.entries_read g ν hi ⟨r, w⟩ hw)

theorem realize_interpreted (g : State C []) (ν : AEnv) {rs : List (ReadOccurrence C)} {start : Nat}
    (h : OccurrenceLayout rs start) (hc : (h.entries g ν).Consistent) :
    ReadOccurrence.All { g with storage := (h.entries g ν).realize } ν rs := by
  intro r hm q hq
  obtain ⟨hr⟩ := h.readFree_mem r hm
  have hp := (r.path_storage hr g ν (h.entries g ν).realize).symm.trans hq
  exact ((Ref.obs_read (⟨r.prim, q, r.guard.declared g ν q hp⟩ : Ref C) _).trans
    (Assignment.read_realize hc (h.entries_contains g ν r hm q hp))).symm

/-- Fill fresh results in dependency order, using actual typed reads. -/
def fill (g : State C []) : {rs : List (ReadOccurrence C)} → {start : Nat} →
    OccurrenceLayout rs start → AEnv → AEnv
  | _, _, .nil _, ν => ν
  | _, start, .cons (r := r) _ _ h tail, ν =>
    tail.fill g (ν.set r.prim start (r.value h g ν))

theorem fill_agrees (g : State C []) {rs : List (ReadOccurrence C)} {start : Nat}
    (h : OccurrenceLayout rs start) (ν : AEnv) : ν.AgreesBelow start (h.fill g ν) := by
  induction h generalizing ν with
  | nil => exact fun _ _ _ => rfl
  | @cons r rs start hs hb hr tail ih =>
    intro p k hk
    exact (AEnv.get_set_ne ν r.prim p _ (Nat.ne_of_lt hk)).symm.trans
      (ih _ p k (Nat.lt_trans hk (Nat.lt_succ_self start)))

theorem fill_interpreted (g : State C []) {rs : List (ReadOccurrence C)} {start : Nat}
    (h : OccurrenceLayout rs start) (ν : AEnv) : ReadOccurrence.All g (h.fill g ν) rs := by
  induction h generalizing ν with
  | nil => exact fun _ h => nomatch h
  | @cons r rs start hs hb hr tail ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · intro q hq
      have hp : x.path.eval g ν = x.path.eval g (fill g (.cons hs hb hr tail) ν) := by
        simpa only [SPath.eval_toLTm] using x.path.toLTm.eval_agree_below g
          ((fill_agrees g (.cons hs hb hr tail) ν).mono hb)
      exact ((tail.fill_agrees g _ _ x.slot (hs ▸ Nat.lt_succ_self start)).symm.trans
        (hs ▸ AEnv.get_set_self ν x.prim start (x.value hr g ν))).trans
          (x.value_eq hr g ν q (hp.trans hq))
    · exact ih _ x hx

end OccurrenceLayout

end Solidity.Decide
