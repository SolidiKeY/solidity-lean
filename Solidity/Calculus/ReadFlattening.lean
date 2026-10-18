import Solidity.Calculus.OccurrenceLayout

/-!
# Exact source flattening and storage reconstruction

The checked layout supplies both directions: every actual storage fills
fresh occurrence atoms, and every alias-consistent active assignment has
an actual storage representative. Read-free output retains the original
failure semantics. Arithmetic compilation is a later stage.
-/

namespace Solidity.Decide

open Semantics ReadRealization

variable {C : Contract}

theorem ReadFormula.holds_agree_below {φ : LFml C} (r : ReadFormula φ) (g : State C [])
    {ν μ : AEnv} (h : ν.AgreesBelow φ.atomBound μ) : φ.holds g ν ↔ φ.holds g μ := by
  induction r with
  | tt => rfl
  | @eq p t w a b =>
    simp only [LFml.holds, t.eval_agree_below g (h.mono (Nat.le_max_left _ _)),
      w.eval_agree_below g (h.mono (Nat.le_max_right _ _))]
  | not r ih => exact not_congr (ih h)
  | and r s ihr ihs =>
    exact and_congr (ihr (h.mono (Nat.le_max_left _ _)))
      (ihs (h.mono (Nat.le_max_right _ _)))
  | imp r s ihr ihs =>
    exact imp_congr (ihr (h.mono (Nat.le_max_left _ _)))
      (ihs (h.mono (Nat.le_max_right _ _)))

/-- Source recognition, freshness and storage independence are checked
separately from the local flattening equivalence. -/
structure ReadFlattening (φ : LFml C) (start : Nat) where
  flat : FlattenedFormula φ start
  source : ReadFormula φ
  bound : φ.atomBound ≤ start
  layout : OccurrenceLayout flat.reads start
  readFree : ReadFreeFormula flat.formula

def readFlatten? (budget : Nat) (φ : LFml C) : Option (ReadFlattening φ φ.atomBound) := do
  let flat ← flattenFormula? budget φ
  return ⟨flat, ← ReadFormula.ofFormula? φ, Nat.le_refl _,
    ← occurrenceLayout? budget flat.reads φ.atomBound, ← readFreeFormula? flat.formula⟩

namespace ReadFlattening

/-- All actual source states are represented without changing their inputs. -/
theorem fill_iff {φ : LFml C} {start : Nat} (r : ReadFlattening φ start)
    (g : State C []) (ν : AEnv) :
    r.flat.formula.holds g (r.layout.fill g ν) ↔ φ.holds g ν :=
  (r.flat.correct g _ (r.layout.fill_interpreted g ν)).trans
    (r.source.holds_agree_below g ((r.layout.fill_agrees g ν).mono r.bound)).symm

/-- A false consistent flattened assignment reconstructs an actual
counterstate to the original leaf, with the same typed atom inputs. -/
def countermodel {φ : LFml C} {start : Nat} (r : ReadFlattening φ start)
    (g : State C []) (ν : AEnv) (hc : (r.layout.entries g ν).Consistent)
    (hf : ¬ r.flat.formula.holds g ν) : {st : State C [] // ¬ φ.holds st ν} :=
  ⟨{ g with storage := (r.layout.entries g ν).realize }, fun hv => hf
    ((r.readFree.holds_storage g ν _).mp
      ((r.flat.correct _ ν (r.layout.realize_interpreted g ν hc)).mpr hv))⟩

/-- Validity is exactly validity of the flattened leaf under active-read
alias consistency. Unsupported syntax and budget limits have no verdict. -/
theorem valid_iff {φ : LFml C} {start : Nat} (r : ReadFlattening φ start) :
    φ.Valid ↔ ∀ (g : State C []) (ν : AEnv),
      (r.layout.entries g ν).Consistent → r.flat.formula.holds g ν := by
  constructor
  · intro hv g ν hc
    exact (r.readFree.holds_storage g ν _).mp
      ((r.flat.correct _ ν (r.layout.realize_interpreted g ν hc)).mpr (hv _ ν))
  · intro hv g ν
    exact (r.fill_iff g ν).mp
      (hv g _ (r.layout.entries_consistent g _ (r.layout.fill_interpreted g ν)))

end ReadFlattening

end Solidity.Decide
