import Solidity.Calculus.TermEq

/-!
# A test point for two integer thresholds

`∀ y : Int, y > z → y > k` is exactly `z ≥ k`: when `z < k`,
the test point `y = k` refutes the implication. The recognizer keeps its
intrinsic shape certificate. Its thresholds are an outer KeY-int local
and an integer literal, so both are total and independent of `y`.

This is a Lean-only exact arithmetic preparation, not general quantifier
elimination. It introduces no term or formula syntax. The existing `zcmp`
and literal printers apply, and nonlinear or differently shaped bodies
are left to the existing pipelines.
-/

namespace Solidity

variable {C : Contract}

/-- The consequent threshold is a counterexample point whenever the
universal implication fails. -/
theorem kint_twoAnchor_order (a b : Int) :
    (∀ y : Int, a < y → b < y) ↔ b ≤ a := by
  grind

/-- The supported body, with the outer local preserved at its position. -/
def Fml.kintTwoAnchorBody {Γ : Ctx} (i : Idx Γ .kint) (k : Int) : Fml C (.kint :: Γ) :=
  .imp
    (.eq (.app2 (.zcmp .gt rfl) (.pvZ .here) (.pvZ (.there i))) (.app0 (.lit true)))
    (.eq (.app2 (.zcmp .gt rfl) (.pvZ .here) (.app0 (.zlit k))) (.app0 (.lit true)))

/-- The exact result of eliminating the inner binder. -/
def Fml.kintTwoAnchorResult {Γ : Ctx} (i : Idx Γ .kint) (k : Int) : Fml C Γ :=
  .eq (.app2 (.zcmp .ge rfl) (.pvZ i) (.app0 (.zlit k))) (.app0 (.lit true))

/-- A successful recognition carries equality to the original typed body. -/
structure KIntTwoAnchorView {Γ : Ctx} (A : Fml C (.kint :: Γ)) where
  index : Idx Γ .kint
  threshold : Int
  shape : A = Fml.kintTwoAnchorBody index threshold

/-- A certified implication head; its context stays generalized in the eliminator. -/
private structure KIntImpView {Γ : Ctx} (A : Fml C Γ) where
  left : Fml C Γ
  right : Fml C Γ
  shape : A = .imp left right

private def kintImpView? {Γ : Ctx} (A : Fml C Γ) : Option (KIntImpView A) :=
  Fml.casesOn (motive := fun _ A => Option (KIntImpView A))
    (tt := none) (eq := fun _ _ => none) (wellFormed := fun _ => none)
    (not := fun _ => none) (and := fun _ _ => none)
    (imp := fun a b => some ⟨a, b, rfl⟩)
    (upd := fun _ _ _ => none) (modal := fun _ _ _ _ => none)
    (havoc := fun _ => none) (all := fun _ _ _ => none)
    (bind := fun _ _ _ _ => none) (anon := fun _ _ => none)
    (allocAll := fun _ _ _ => none) (grow := fun _ => none) A

/-- A certified strict integer comparison observed as Boolean true. -/
private structure KIntGtView {Γ : Ctx} (A : Fml C Γ) where
  lhs : Tm C Γ .kint
  rhs : Tm C Γ .kint
  shape : A = .eq (.app2 (.zcmp .gt rfl) lhs rhs) (.app0 (.lit true))

private def kintGtView? {Γ : Ctx} (A : Fml C Γ) : Option (KIntGtView A) :=
  Fml.casesOn (motive := fun _ A => Option (KIntGtView A))
    (tt := none)
    (eq := @fun Γ p a b => match p, a with
      | .bool, .app2 (.zcmp .gt _) lhs rhs =>
        if ht : b.beqR (.app0 (.lit (p := .bool) true)) = true then
          some ⟨lhs, rhs, by rw [Tm.eq_of_beqR ht]⟩
        else none
      | _, _ => none)
    (wellFormed := fun _ => none) (not := fun _ => none) (and := fun _ _ => none)
    (imp := fun _ _ => none) (upd := fun _ _ _ => none) (modal := fun _ _ _ _ => none)
    (havoc := fun _ => none) (all := fun _ _ _ => none)
    (bind := fun _ _ _ _ => none) (anon := fun _ _ => none)
    (allocAll := fun _ _ _ => none) (grow := fun _ => none) A

/-- Shallow recursor-based formula views keep G0's context index generalized.
Only fixed-constructor term inspections remain, with the context a parameter. -/
def Fml.kintTwoAnchorView? {Γ : Ctx} (A : Fml C (.kint :: Γ)) : Option (KIntTwoAnchorView A) := do
  let v ← kintImpView? A
  let a ← kintGtView? v.left
  let b ← kintGtView? v.right
  match hl : a.lhs, ht : a.rhs, hr : b.lhs, hk : b.rhs with
  | .pvZ .here, .pvZ (.there i), .pvZ .here, .app0 (.zlit k) =>
    some ⟨i, k, by
      simp only [v.shape, a.shape, b.shape, hl, ht, hr, hk, Fml.kintTwoAnchorBody]
    ⟩
  | _, _, _, _ => none

/-- Exact at every typed state, under either hidden-binder modality. -/
theorem Fml.holds_kintTwoAnchor {Γ : Ctx} (i : Idx Γ .kint) (k : Int)
    (m : Modality) (x : Var) (σ : State C Γ) :
    holds σ (Fml.kintTwoAnchorResult i k) ↔
      holds σ (.bind m x .kint (Fml.kintTwoAnchorBody i k)) := by
  change ((some (decide (k ≤ TEnv.get i σ.env)) : Option Bool) = some true) ↔
    ∀ y : Int, (some (decide (TEnv.get i σ.env < y)) : Option Bool) = some true →
      (some (decide (k < y)) : Option Bool) = some true
  simpa only [Option.some.injEq, decide_eq_true_eq] using
    (kint_twoAnchor_order (TEnv.get i σ.env) k).symm

/-- A recognized body inherits the exact test-point equivalence. -/
theorem KIntTwoAnchorView.holds {Γ : Ctx} {A : Fml C (.kint :: Γ)}
    (v : KIntTwoAnchorView A) (m : Modality) (x : Var) (σ : State C Γ) :
    holds σ (Fml.kintTwoAnchorResult v.index v.threshold) ↔ holds σ (.bind m x .kint A) := by
  rcases v with ⟨i, k, rfl⟩
  exact Fml.holds_kintTwoAnchor i k m x σ

#print axioms kint_twoAnchor_order
#print axioms Fml.holds_kintTwoAnchor
#print axioms KIntTwoAnchorView.holds

end Solidity
