import Solidity.Calculus.TypedLinear
import Solidity.Calculus.ReadRealization

/-!
# Typed arithmetic assignments as actual storage

A layout lists distinct actual primitive locations. Its heterogeneous
vector is exactly the values read from those locations. Every such vector
has a storage representative, built by successful interpreter saves.
Aliased occurrences must share a layout entry; treating them as distinct
variables would invalidate the realization law.
-/

namespace Solidity.ReadRealization

open Linear ScalarCode

variable {C : Contract}

namespace Layout

def types (rs : List (Ref C)) : List PrimTy := rs.map Ref.prim

def observe : (rs : List (Ref C)) → Storage C → Values (types rs)
  | [], _ => ()
  | r :: rs, st => (r.read st, observe rs st)

def realize : (rs : List (Ref C)) → Values (types rs) → Storage C
  | [], _ => Storage.init C
  | r :: rs, vs => r.write vs.1 (realize rs vs.2)

/-- Occurrences of an alias choose the same numbered variable. An absent
reference chooses the length; clients must prove membership before use. -/
def index (r : Ref C) : List (Ref C) → Nat
  | [] => 0
  | q :: rs => if r = q then 0 else index r rs + 1

theorem codes_index (rs : List (Ref C)) (r : Ref C) (st : Storage C) (h : r ∈ rs) :
    (observe rs st).codes (index r rs) = (encode r.prim (r.read st)).val := by
  induction rs with
  | nil => cases h
  | cons q qs ih =>
    by_cases he : r = q
    · subst r
      simp only [index, ↓reduceIte, observe, Values.codes]
    · simp only [index, he, ↓reduceIte, observe, Values.codes]
      exact ih ((List.mem_cons.mp h).resolve_left he)

/-- Candidate layout deduplication. Its clients check coverage and
distinctness explicitly before constructing a semantic certificate. -/
def unique : List (Ref C) → List (Ref C)
  | [] => []
  | r :: rs => let tail := unique rs; if r ∈ tail then tail else r :: tail

theorem observe_write_ne (rs : List (Ref C)) (r : Ref C) (v : r.Value)
    (st : Storage C) (h : r ∉ rs) : observe rs (r.write v st) = observe rs st := by
  induction rs with
  | nil => rfl
  | cons q qs ih =>
    have hne : r ≠ q := fun he => h (he ▸ List.mem_cons_self)
    have ht : r ∉ qs := fun hm => h (List.mem_cons_of_mem q hm)
    simp only [observe, Ref.read_write_ne hne, ih ht]

/-- No alias constraints are omitted: distinct actual locations can be
assigned independently, while repeated locations are excluded. -/
theorem observe_realize (rs : List (Ref C)) (hn : rs.Nodup) (vs : Values (types rs)) :
    observe rs (realize rs vs) = vs := by
  induction rs with
  | nil => cases vs; rfl
  | cons r rs ih =>
    have hp := List.nodup_cons.mp hn
    change (r.read (r.write vs.1 (realize rs vs.2)), observe rs (r.write vs.1 (realize rs vs.2))) = vs
    rw [r.read_write, observe_write_ne rs r vs.1 _ hp.1, ih hp.2 vs.2]
    rfl

/-- A complete arithmetic sentence on a finite layout. Its variables are
the exact scalar codes of the corresponding actual storage values. -/
abbrev Formula (rs : List (Ref C)) := TypedFormula (types rs)

/-- The linear validity decision is exact for all storage reads of a
distinct layout, not just a candidate pool or a bounded search. -/
theorem valid_iff (rs : List (Ref C)) (hn : rs.Nodup) (F : Formula rs) :
    F.Valid ↔ ∀ st : Storage C, F.holds (observe rs st) := by
  constructor
  · intro h st; exact h _
  · intro h vs
    have hv := h (realize rs vs)
    rw [observe_realize rs hn vs] at hv
    exact hv

/-- One arithmetic graph traversal either proves every storage assignment
or saves the decoded false vector into an actual typed storage. -/
def verify (rs : List (Ref C)) (hn : rs.Nodup) (F : Formula rs) :
    Sum (PLift (∀ st : Storage C, F.holds (observe rs st)))
      { st : Storage C // ¬ F.holds (observe rs st) } := by
  match F.verify with
  | .inl h => exact .inl ⟨(valid_iff rs hn F).1 h.down⟩
  | .inr cm =>
    refine .inr ⟨realize rs cm.val, ?_⟩
    rw [observe_realize rs hn cm.val]
    exact cm.property

end Layout

end Solidity.ReadRealization
