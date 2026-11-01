import Solidity.Calculus.Decision

/-!
# A sharp source-coefficient boundary for a program-free family

For a closed typed uint term `c`, the family is `∀ uint x; c * x = x + x`.
The source coefficient need not be state-independent or covered. This module
characterizes admission by direct literal shape, independently of lowering.
It does not assert the old unconditional Covered-to-target inclusion or the
full M4 source characterization. Other formula shapes, additional/negative or hidden
binders, updates/programs and other right-hand sides are outside this family;
state reads inside the closed coefficient itself are allowed. Both existing
predicate definitions are intact.
-/
namespace Solidity.Decide.CoefficientBoundary

/-- The program-free coefficient family; weakening keeps `c` independent of `x`. -/
def coefficientLeaf {C : Contract} (c : Tm C [] (.val .uint)) : Fml C [] :=
  .all (.user "x") .uint
    (.eq (.app2 (.binop .mul rfl) (c.wk (.drop .refl)) (.pvV .here))
      (.app2 (.binop .add rfl) (.pvV .here) (.pvV .here)))

/-- Weakening changes local indices, never direct-literal source shape. -/
theorem isLitV_wk {C : Contract} {Γ Δ : Ctx} {s : Srt}
    (h : Thin Γ Δ) (t : Tm C Γ s) : (t.wk h).isLitV = t.isLitV := by
  cases t <;> rfl

/-- A direct source literal satisfies term admission; nonliterals mask the guard. -/
theorem literal_admission {C : Contract} {Γ : Ctx} {s : Srt}
    (w : Waivers) (hashOK : Bool) (t : Tm C Γ s) :
    (t.inTarget w hashOK && t.isLitV) = t.isLitV := by
  cases t <;> simp only [Tm.inTarget, Tm.isLitV, Tm.litValue?, Option.isSome, Bool.and_false, Bool.true_and]

/-- At positive prefix polarity, a universal value binder preserves body admission. -/
theorem target_all_positive {C : Contract} {Γ : Ctx} (w : Waivers)
    (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    (Fml.all x p φ).target w true false = φ.target w true false := by
  cases h : φ.readsAt [Γ.length] <;> simp only [Fml.target, h] <;> rfl

/-- The family's operator-admission component is exactly the coefficient guard. -/
theorem coefficientLeaf_target {C : Contract} (w : Waivers)
    (c : Tm C [] (.val .uint)) :
    (coefficientLeaf c).target w true false = c.isLitV := by
  unfold coefficientLeaf
  rw [target_all_positive]
  let ρ : Thin ([] : Ctx) [.val .uint] := .drop .refl
  change (((c.wk ρ).inTarget w false && true && ((c.wk ρ).isLitV || false)) && true) = c.isLitV
  simp only [Bool.and_true, Bool.or_false]
  rw [literal_admission]
  exact isLitV_wk ρ c

/-- No negative-position value binder occurs in the family, even for a hash coefficient. -/
theorem coefficientLeaf_negPairUnread {C : Contract} (c : Tm C [] (.val .uint)) :
    (coefficientLeaf c).negPairUnread (coefficientLeaf c).scopeHashes true = false := by
  rfl

/-- Only the coefficient can contribute mapping keys to this family. -/
theorem coefficientLeaf_mapKeys {C : Contract} (c : Tm C [] (.val .uint)) :
    (coefficientLeaf c).mapKeys = (c.wk (.drop (.refl : Thin [] [])) : Tm C [.val .uint] (.val .uint)).mapKeys := by
  let ρ : Thin ([] : Ctx) [.val .uint] := .drop .refl
  change (([] ++ (c.wk ρ).mapKeys ++ []) ++ ([] ++ [] ++ [])) = (c.wk ρ).mapKeys
  simp only [List.nil_append, List.append_nil]

/-- Literal coefficients have no mapping keys; nonliteral coefficients mask this check. -/
theorem literal_keys {C : Contract} {Γ : Ctx} {s : Srt} (t : Tm C Γ s) :
    (t.isLitV && keysAgree t.mapKeys) = t.isLitV := by
  cases t <;> simp only [Tm.isLitV, Tm.litValue?, Option.isSome, Bool.false_and]
  simp only [Tm.mapKeys, keysAgree, List.all_nil, Bool.and_true]

/-- The exact source boundary, for every contract, waiver setting and closed typed coefficient.
Coverage is not a hypothesis: admission in this family is exactly direct literal shape. -/
theorem coefficientLeaf_inTarget {C : Contract} (w : Waivers)
    (c : Tm C [] (.val .uint)) : (coefficientLeaf c).inTarget w = c.isLitV := by
  unfold Fml.inTarget
  rw [coefficientLeaf_target, coefficientLeaf_negPairUnread]
  simp only [Bool.not_false, Bool.and_true]
  rw [coefficientLeaf_mapKeys]
  let ρ : Thin ([] : Ctx) [.val .uint] := .drop .refl
  simpa only [isLitV_wk] using literal_keys (c.wk ρ)

/-- On covered members of this explicitly stated family, source admission holds exactly
for literal coefficients. This is not the old unrestricted reverse inclusion. -/
theorem covered_boundary {C : Contract} (w : Waivers) (c : Tm C [] (.val .uint))
    (_coverage : (coefficientLeaf c).Covered = true) :
    ((coefficientLeaf c).inTarget w = true ↔ c.isLitV = true) := by
  rw [coefficientLeaf_inTarget]

end Solidity.Decide.CoefficientBoundary
