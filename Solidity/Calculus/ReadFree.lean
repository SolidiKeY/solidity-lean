import Solidity.Calculus.QueryReadBounds

/-!
# Executable read-free leaf terms

The existing typed query recognizer supplies computation; its proved zero
read bound guarantees storage independence. This is used for flattened
keys and values when constructing occurrence assignments from fresh atoms.
-/

namespace Solidity.Decide

open Semantics ReadRealization

variable {C : Contract}

structure ReadFree {s : Srt} (t : LTm C s) where
  query : ReadExpr t
  zero : query.readBound = 0

def readFree? {s : Srt} (t : LTm C s) : Option (ReadFree t) := do
  let q ← ReadExpr.ofTerm? t
  if h : q.readBound = 0 then return ⟨q, h⟩ else none

private theorem runStorage_eq_of_zero {α : Type} (q : Query C α) (h : q.Within 0)
    (a b : Storage C) : q.runStorage a = q.runStorage b := by
  cases q with
  | pure x => rfl
  | read r k =>
    have hn := h (fun _ p => PrimTy.dflt p) 0
    simp only [Query.replay, List.length_cons, Nat.add_one_le_iff, Nat.not_lt_zero] at hn

/-- A certified read-free term has the same optional value in every
storage, retaining the state's other typed components and atom environment. -/
theorem ReadFree.eval_storage {s : Srt} {t : LTm C s} (r : ReadFree t)
    (g : State C []) (ν : AEnv) (st : Storage C) :
    t.eval { g with storage := st } ν = t.eval g ν := by
  exact (r.query.query_sound g ν st).symm.trans
    ((congrArg (Option.map (ReadDen.erase g))
      (runStorage_eq_of_zero _ (r.zero ▸ r.query.query_within g ν) st g.storage)).trans
      (r.query.query_sound g ν g.storage))

structure ReadFreeFormula (φ : LFml C) where
  query : ReadFormula φ
  zero : query.readBound = 0

def readFreeFormula? (φ : LFml C) : Option (ReadFreeFormula φ) := do
  let q ← ReadFormula.ofFormula? φ
  if h : q.readBound = 0 then return ⟨q, h⟩ else none

theorem ReadFreeFormula.holds_storage {φ : LFml C} (r : ReadFreeFormula φ)
    (g : State C []) (ν : AEnv) (st : Storage C) :
    φ.holds { g with storage := st } ν ↔ φ.holds g ν := by
  rw [← r.query.query_iff g ν st, ← r.query.query_iff g ν g.storage,
    runStorage_eq_of_zero _ (r.zero ▸ r.query.query_within g ν) st g.storage]

end Solidity.Decide
