import Solidity.Calculus.ReadFlattening

/-!
# Alias constraints guarded by successful paths

Only successful occurrences require alias agreement. The generated formula
uses the existing path comparison and definedness guards; its meaning is
exactly consistency of the actual active assignment, including failed keys.
-/

namespace Solidity.Decide

open Semantics ReadRealization

variable {C : Contract}

namespace ReadOccurrence

def witness (r : ReadOccurrence C) (g : State C []) (ν : AEnv)
    (q : SRef C (.prim r.prim)) (hq : r.path.eval g ν = some q) :
    SymbolicRead.Witness g ν r.symbolic :=
  ⟨q, r.guard.declared g ν q hq, ν.get r.prim r.slot, hq, rfl⟩

theorem guard_holds (r : ReadOccurrence C) (g : State C []) (ν : AEnv) :
    (LFml.rets r.guard.test).holds g ν ↔ ∃ q, r.path.eval g ν = some q := by
  rw [LFml.holds_rets, r.guard.correct g ν]
  cases r.path.eval g ν <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq, exists_false, exists_eq']

def constraint (r q : ReadOccurrence C) : LFml C :=
  .imp (.rets r.guard.test) (.imp (.rets q.guard.test) (r.symbolic.constraint q.symbolic))

theorem constraint_holds (r q : ReadOccurrence C) (g : State C []) (ν : AEnv) :
    (r.constraint q).holds g ν ↔
      ∀ (wr : SymbolicRead.Witness g ν r.symbolic) (wq : SymbolicRead.Witness g ν q.symbolic),
        Assignment.Consistent [wr.entry, wq.entry] := by
  constructor
  · intro h wr wq
    exact (SymbolicRead.constraint_holds g ν _ _ wr wq).mp
      (h ((r.guard_holds g ν).mpr ⟨wr.ref, wr.path_eq⟩)
        ((q.guard_holds g ν).mpr ⟨wq.ref, wq.path_eq⟩))
  · intro h hr hq
    obtain ⟨pr, hp⟩ := (r.guard_holds g ν).mp hr
    obtain ⟨qr, hq'⟩ := (q.guard_holds g ν).mp hq
    exact (SymbolicRead.constraint_holds g ν _ _ (r.witness g ν pr hp) (q.witness g ν qr hq')).mpr (h _ _)

def conjunction : List (LFml C) → LFml C
  | [] => .tt
  | φ :: fs => .and φ (conjunction fs)

theorem conjunction_holds (g : State C []) (ν : AEnv) (fs : List (LFml C)) :
    (conjunction fs).holds g ν ↔ ∀ φ ∈ fs, φ.holds g ν := by
  induction fs with
  | nil => simp only [conjunction, LFml.holds, List.not_mem_nil, false_implies, implies_true]
  | cons φ fs ih => simp only [conjunction, LFml.holds, ih, List.forall_mem_cons]

def constraints (rs : List (ReadOccurrence C)) : LFml C :=
  conjunction (rs.flatMap fun r => rs.map fun q => r.constraint q)

theorem constraints_holds (rs : List (ReadOccurrence C)) (g : State C []) (ν : AEnv) :
    (constraints rs).holds g ν ↔ ∀ r ∈ rs, ∀ q ∈ rs, (r.constraint q).holds g ν := by
  rw [constraints, conjunction_holds]
  constructor
  · intro h r hr q hq
    exact h _ (List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨q, hq, rfl⟩⟩)
  · intro h φ hφ
    obtain ⟨r, hr, hm⟩ := List.mem_flatMap.mp hφ
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact h r hr q hq

end ReadOccurrence

namespace OccurrenceLayout

theorem entries_witness (g : State C []) (ν : AEnv) {rs : List (ReadOccurrence C)} {start : Nat}
    (h : OccurrenceLayout rs start) (r : ReadOccurrence C) (hm : r ∈ rs)
    (w : SymbolicRead.Witness g ν r.symbolic) : w.entry ∈ h.entries g ν := by
  have hv : ν.get r.prim r.slot = w.value := Option.some.inj w.result_eq
  simpa only [SymbolicRead.Witness.entry, ReadOccurrence.symbolic, hv] using
    h.entries_contains g ν r hm w.ref w.path_eq

theorem entries_origin (g : State C []) (ν : AEnv) {rs : List (ReadOccurrence C)} {start : Nat}
    (h : OccurrenceLayout rs start) (e : (r : Ref C) × r.Value) (he : e ∈ h.entries g ν) :
    ∃ r ∈ rs, ∃ w : SymbolicRead.Witness g ν r.symbolic, w.entry = e := by
  induction h with
  | nil => cases he
  | @cons r rs start hs hb hr tail ih =>
    cases hx : r.location? hr g ν with
    | none =>
      obtain ⟨x, hm, w, hw⟩ := ih (by simpa only [entries, hx] using he)
      exact ⟨x, List.mem_cons_of_mem _ hm, w, hw⟩
    | some q =>
      rcases List.mem_cons.mp (show e ∈ _ :: tail.entries g ν by simpa only [entries, hx] using he) with he | he
      · subst e
        exact ⟨r, List.mem_cons_self, r.witness g ν q.val
          ((r.location?_eq hr g ν).symm.trans (congrArg (Option.map Subtype.val) hx)), rfl⟩
      · obtain ⟨x, hm, w, hw⟩ := ih he
        exact ⟨x, List.mem_cons_of_mem _ hm, w, hw⟩

/-- No alias condition is imposed on a failed path, and none is omitted
between successful occurrences. -/
theorem constraints_iff (g : State C []) (ν : AEnv) {rs : List (ReadOccurrence C)} {start : Nat}
    (h : OccurrenceLayout rs start) :
    (ReadOccurrence.constraints rs).holds g ν ↔ (h.entries g ν).Consistent := by
  rw [ReadOccurrence.constraints_holds]
  constructor
  · intro hf r v w hv hw
    obtain ⟨x, hx, wx, ex⟩ := h.entries_origin g ν ⟨r, v⟩ hv
    obtain ⟨y, hy, wy, ey⟩ := h.entries_origin g ν ⟨r, w⟩ hw
    exact ((ReadOccurrence.constraint_holds x y g ν).mp (hf x hx y hy) wx wy) r v w
      (List.mem_cons.mpr (Or.inl ex.symm))
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl ey.symm))))
  · intro hc x hx y hy
    apply (ReadOccurrence.constraint_holds x y g ν).mpr
    intro wx wy
    have hm : ∀ e ∈ [wx.entry, wy.entry], e ∈ h.entries g ν := by
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact h.entries_witness g ν x hx wx
      · rw [List.mem_singleton.mp he]
        exact h.entries_witness g ν y hy wy
    exact fun r v w hv hw => hc r v w (hm _ hv) (hm _ hw)

end OccurrenceLayout

namespace ReadFlattening

def formula {φ : LFml C} {start : Nat} (r : ReadFlattening φ start) : LFml C :=
  .imp (ReadOccurrence.constraints r.flat.reads) r.flat.formula

theorem formula_valid_iff {φ : LFml C} {start : Nat} (r : ReadFlattening φ start) :
    r.formula.Valid ↔ φ.Valid := by
  simpa only [formula, LFml.Valid, LFml.holds, r.layout.constraints_iff] using r.valid_iff.symm

end ReadFlattening

end Solidity.Decide
