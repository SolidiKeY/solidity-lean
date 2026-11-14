import Solidity.Examples.DecisionKInt

/-!
# KeY-`int` binders past the two-word encoding: the Residue shape, pinned

A negative KeY-`int` binder is decided by encoding it over two words
(`Fml.kencB`, `Calculus/KIntEncode.lean`); the encoding's multiplier `zMul n`
must fit a word, which bounds the literals it can compare against at about
`2^511`. The three members below, past that bound, are in the target and not
covered (pinned examples, not a general theorem). The same statement at a
small literal is covered. These pins narrow the Residue shape;
they do not decide it. (`negBig` is false: its hypothesis holds; `negBigGood`
and `nestedBig` are valid: their hypotheses fail.)
-/
namespace Solidity.Examples.DecisionGapKIntResidue
open Solidity.Decide Solidity.Examples.Decision Solidity.Examples.DecisionKInt
set_option Elab.async false

/-- `2^600`, past the encoding's word. -/
def big : Int := 2 ^ 600

/-- `(∀ int z. z > 0 → z > 5) → 0 == 1`: covered at a small literal. -/
def negSmall : Fml Gaps [] := .imp (bindZ "z" (.imp (zcmp .gt rfl zv (zlit 0)) (zcmp .gt rfl zv (zlit 5)))) ff
/-- `(∀ int z. z > 0 → z > -2^600) → 0 == 1`: false, not covered. -/
def negBig : Fml Gaps [] := .imp (bindZ "z" (.imp (zcmp .gt rfl zv (zlit 0)) (zcmp .gt rfl zv (zlit (-big))))) ff
/-- `(∀ int z. z > 0 → z > 2^600) → 0 == 1`: valid, not covered. -/
def negBigGood : Fml Gaps [] := .imp (bindZ "z" (.imp (zcmp .gt rfl zv (zlit 0)) (zcmp .gt rfl zv (zlit big)))) ff
/-- `(∀ int z. ∀ int y. y > z + 2^600) → 0 == 1`: valid, not covered. -/
def nestedBig : Fml Gaps [] := .imp (bindZ "z" (bindZ "y" (zcmp .gt rfl zv (zplus (.pvZ (.there .here)) (zlit big))))) ff

/-- The small-literal control is in the target and covered through the encoding. -/
theorem small_covered : negSmall.inTarget {} = true ∧ negSmall.kencB.2 = true ∧
    negSmall.Covered = true := by decide +kernel

/-- Past the word: in the target, refused by the encoding, not covered. -/
theorem big_residue : [negBig, negBigGood, nestedBig].all
    (fun φ => φ.inTarget {} && !φ.kencB.2 && !φ.Covered) = true := by decide +kernel

/-- The large positive bound fails already at `z = 1`, so the implication is valid. -/
theorem negBigGood_valid : Fml.Valid negBigGood := by
  intro σ h
  have hh := h (1 : Int) (by rfl)
  change (some (decide (big < (1 : Int))) : Option Bool) = some true at hh
  exact False.elim ((by decide +kernel :
    ¬ ((some (decide (big < (1 : Int))) : Option Bool) = some true)) hh)

/-- Every positive integer exceeds the large negative bound; the conclusion is false. -/
theorem negBig_countermodel (σ : State Gaps []) : ¬ holds σ negBig := by
  intro h
  have hc := h (by
    change ∀ z : Int, (some (decide (0 < z)) : Option Bool) = some true →
      (some (decide (-big < z)) : Option Bool) = some true
    simp only [Option.some.injEq, decide_eq_true_eq]
    intro z hz
    have hb : 0 < big := by decide +kernel
    omega)
  change (some (uintOfNat 0) : Option PrimTy.uint.Denote) = some (uintOfNat 1) at hc
  exact (by decide +kernel :
    (some (uintOfNat 0) : Option PrimTy.uint.Denote) ≠ some (uintOfNat 1)) hc

/-- The negative large-bound implication has a typed countermodel. -/
theorem negBig_notValid : ¬ Fml.Valid negBig :=
  fun h => negBig_countermodel (State.init Gaps) (h _)

end Solidity.Examples.DecisionGapKIntResidue
