import Solidity.Examples.Decision

/-!
# Binders of KeY's `int` over two words (M7, features 30 and 31)

`decideKEnc` (`Calculus/Decision.lean`, `Calculus/KIntEncode.lean`) reads a
binder of KeY's `int` whose comparisons read it against bounded terms over
two words, at every state (feature 30), past an anchor of its context
where they read it against one unbounded term (feature 31).  The former
counterexample `gapKIntNeg`, a negative binder (an `∃` over `ℤ`), is
proved, its false variant refuted; a positive binder in a leaf reading the
ledger elsewhere (outside feature 26, which needs the ledger free) is
proved and refuted; a binder compared with a ledger entry (`kintNet`) and
two binders compared under a negation (`kintNested`) are decided past
their anchors.  Coverage is the kernel's (`*_covered`), so each is
answered and exactly (`*_answers`, `*_iff`); the verdicts are recorded
below. The original `gapKIntTwoAnchors` statement is retained and now has
an exact kernel-certified proved verdict: the test point `y = k` reduces
`∀ y. y > z → y > k` to `z >= k`, including under negation. The other
original gap, a negative quantifier in a leaf reading the ledger,
remains (`gapQuantLedger`, `(∀ uint y. y > 0) → net(0) > 0`).
-/

namespace Solidity.Examples.DecisionKInt

open Solidity.Decide Solidity.Examples.Decision

/-- `z` and `net(0)` of KeY's `int`; `ff` is `0 == 1`. -/
def zv {Γ : Ctx} : Tm Gaps (.kint :: Γ) .kint := .pvZ .here
def zlit {Γ : Ctx} (n : Int) : Tm Gaps Γ .kint := .app0 (.zlit n)
def net0 {Γ : Ctx} : Tm Gaps Γ .kint := .app1 .net (litU 0)
def zcmp {Γ : Ctx} (op : BinOp) (h : op.zCmp = true) (a b : Tm Gaps Γ .kint) : Fml Gaps Γ :=
  isT (.app2 (.zcmp op h) a b)
def zplus {Γ : Ctx} (a b : Tm Gaps Γ .kint) : Tm Gaps Γ .kint := .app2 (.zbin .add rfl) a b
def bindZ {Γ : Ctx} (x : String) (φ : Fml Gaps (.kint :: Γ)) : Fml Gaps Γ := .bind .box (.user x) .kint φ
def ff {Γ : Ctx} : Fml Gaps Γ := .eq (litU 0) (litU 1)

/-- The false variant of `gapKIntNeg`: `(∀ int z. z > 0 → z > -5) → 0 == 1`
(the hypothesis holds). -/
def kintNegBad : Fml Gaps [] :=
  .imp (bindZ "z" (.imp (zcmp .gt rfl zv (zlit 0)) (zcmp .gt rfl zv (zlit (-5))))) ff

/-- A positive binder in a leaf that reads the ledger elsewhere:
`∀ int z. net(0) >= 0 → z + 1 > z`, and its false variant
`∀ int z. net(0) >= 0 → z > 5`. -/
def kintNetElse : Fml Gaps [] :=
  bindZ "z" (.imp (zcmp .ge rfl net0 (zlit 0)) (zcmp .gt rfl (zplus zv (zlit 1)) zv))
def kintNetElseBad : Fml Gaps [] :=
  bindZ "z" (.imp (zcmp .ge rfl net0 (zlit 0)) (zcmp .gt rfl zv (zlit 5)))

/-- A binder compared with a `uint` widened, under a negation:
`∀ uint x. (∀ int z. z > toInt(x)) → 0 == 1` (the multiplier `3`). -/
def kintNegWord : Fml Gaps [] :=
  .all (.user "x") .uint (.imp (bindZ "z" (zcmp .gt rfl zv (.app1 .toInt (.pvV (.there .here))))) ff)

/-- Past an anchor (feature 31): a binder compared with a ledger entry,
`∀ int z. net(0) == z → net(0) + 1 > z` (proved, anchor `net(0)`), its
false variant `∀ int z. net(0) == z → net(0) > z`; two binders compared
under a negation, `(∀ int z. ∀ int y. y > z) → 0 == 1` (proved: the
hypothesis fails, anchor `z`), its false variant
`(∀ int z. ∀ int y. y > z → y >= z) → 0 == 1`. -/
def kintNet : Fml Gaps [] :=
  bindZ "z" (.imp (zcmp .eqB rfl net0 zv) (zcmp .gt rfl (zplus net0 (zlit 1)) zv))
def kintNetBad : Fml Gaps [] :=
  bindZ "z" (.imp (zcmp .eqB rfl net0 zv) (zcmp .gt rfl net0 zv))
def kintNested : Fml Gaps [] :=
  .imp (bindZ "z" (bindZ "y" (zcmp .gt rfl zv (.pvZ (.there .here))))) ff
def kintNestedBad : Fml Gaps [] :=
  .imp (bindZ "z" (bindZ "y" (.imp (zcmp .gt rfl zv (.pvZ (.there .here)))
    (zcmp .ge rfl zv (.pvZ (.there .here)))))) ff

/-- The two original gap statements, retained unchanged: two integer
thresholds, and a negative quantifier in a leaf reading the ledger.
The test-point certificates below settle only the former. -/
def gapKIntTwoAnchors : Fml Gaps [] :=
  .imp (bindZ "z" (bindZ "y" (.imp (zcmp .gt rfl zv (.pvZ (.there .here))) (zcmp .gt rfl zv (zlit 0))))) ff
def gapQuantLedger : Fml Gaps [] :=
  .imp (.all (.user "y") .uint (isT (.app2 (.binop .gt rfl) (.pvV .here) (litU 0))))
    (zcmp .gt rfl net0 (zlit 0))

theorem kintNegBad_inTarget : kintNegBad.inTarget {} = true := by decide +kernel
theorem kintNetElse_inTarget : kintNetElse.inTarget {} = true := by decide +kernel
theorem kintNet_inTarget : kintNet.inTarget {} = true := by decide +kernel
theorem kintNested_inTarget : kintNested.inTarget {} = true := by decide +kernel
theorem gapKIntTwoAnchors_inTarget : gapKIntTwoAnchors.inTarget {} = true := by decide +kernel
theorem gapQuantLedger_inTarget : gapQuantLedger.inTarget {} = true := by decide +kernel

theorem gapKIntNeg_covered : gapKIntNeg.Covered = true := by decide +kernel
theorem kintNegBad_covered : kintNegBad.Covered = true := by decide +kernel
theorem kintNetElse_covered : kintNetElse.Covered = true := by decide +kernel
theorem kintNetElseBad_covered : kintNetElseBad.Covered = true := by decide +kernel
theorem kintNet_covered : kintNet.Covered = true := by decide +kernel
theorem kintNetBad_covered : kintNetBad.Covered = true := by decide +kernel
theorem kintNested_covered : kintNested.Covered = true := by decide +kernel
theorem kintNestedBad_covered : kintNestedBad.Covered = true := by decide +kernel

/-- `decideGoal_complete`, applied: no hash, so no premise. -/
theorem gapKIntNeg_answers : decideGoal gapKIntNeg ≠ .unknown :=
  decideGoal_complete gapKIntNeg_covered rfl

/-- `decideLeaf_proved_iff`, applied: the verdict is exact. -/
theorem gapKIntNeg_iff : decideLeaf gapKIntNeg = .proved ↔ Fml.Valid gapKIntNeg :=
  decideLeaf_proved_iff gapKIntNeg_covered

theorem kintNetElse_answers : decideGoal kintNetElse ≠ .unknown :=
  decideGoal_complete kintNetElse_covered rfl

theorem kintNetElse_iff : decideLeaf kintNetElse = .proved ↔ Fml.Valid kintNetElse :=
  decideLeaf_proved_iff kintNetElse_covered

theorem kintNet_iff : decideLeaf kintNet = .proved ↔ Fml.Valid kintNet :=
  decideLeaf_proved_iff kintNet_covered

theorem kintNested_iff : decideLeaf kintNested = .proved ↔ Fml.Valid kintNested :=
  decideLeaf_proved_iff kintNested_covered

/-! The verdicts, evaluated by the interpreter on 2026-10-26 in a scratch
module, are not pinned: in this module's elaboration the interpreted
evaluation overflowed the language server's stack and did not end within
half an hour in `lake build`.  Evaluated: `gapKIntNeg`, `kintNetElse`,
`kintNegWord`, `kintNet`, `kintNested` proved; `kintNegBad`,
`kintNetElseBad`, `kintNetBad`, `kintNestedBad` refuted;
`gapKIntTwoAnchors`, `gapQuantLedger` unknown.  The theorems above are the
pins: coverage by the kernel, so `decideLeaf` answers, and exactly.
The later test-point certificates below supersede only the recorded
`gapKIntTwoAnchors` unknown verdict. -/

theorem kintNegBad_answers : decideLeaf kintNegBad ≠ .unknown := decideLeaf_complete kintNegBad_covered
theorem kintNetElseBad_answers : decideLeaf kintNetElseBad ≠ .unknown :=
  decideLeaf_complete kintNetElseBad_covered
theorem kintNetBad_answers : decideLeaf kintNetBad ≠ .unknown := decideLeaf_complete kintNetBad_covered
theorem kintNestedBad_answers : decideLeaf kintNestedBad ≠ .unknown :=
  decideLeaf_complete kintNestedBad_covered

/-! ## Two-anchor test point

The original gap and its target certificate above are unchanged. These
controls use the existing formula helpers independently of the new view.
-/

/-- `∀ z. z >= k → ∀ y. y > z → y > k`, under either hidden-binder modality. -/
def twoAnchorGood (m : Modality) (k : Int) : Fml Gaps [] :=
  bindZ "z" (.imp (zcmp .ge rfl zv (zlit k))
    (.bind m (.user "y") .kint
      (.imp (zcmp .gt rfl zv (.pvZ (.there .here))) (zcmp .gt rfl zv (zlit k)))))

/-- The false universal premise: `z = k - 1`, `y = k` refutes it. -/
def twoAnchorBad (m : Modality) (k : Int) : Fml Gaps [] :=
  bindZ "z" (.bind m (.user "y") .kint
    (.imp (zcmp .gt rfl zv (.pvZ (.there .here))) (zcmp .gt rfl zv (zlit k))))

theorem twoAnchorGood_covered (m : Modality) : (twoAnchorGood m (-3)).Covered = true := by
  cases m <;> decide +kernel

theorem twoAnchorBad_covered (m : Modality) : (twoAnchorBad m (-3)).Covered = true := by
  cases m <;> decide +kernel

/-- Includes the equality boundary `z = k`, where the implication holds. -/
theorem twoAnchorGood_valid (m : Modality) (k : Int) : Fml.Valid (twoAnchorGood m k) := by
  change ∀ (_σ : State Gaps []) (z : Int),
    (some (decide (k ≤ z)) : Option Bool) = some true → ∀ y : Int,
      (some (decide (z < y)) : Option Bool) = some true →
        (some (decide (k < y)) : Option Bool) = some true
  simpa only [Option.some.injEq, decide_eq_true_eq] using
    (show ∀ (_σ : State Gaps []) (z : Int), k ≤ z → ∀ y : Int, z < y → k < y from
      fun _ _ hz _ hy => by omega)

/-- A typed countermodel at every starting state, with the bound values
`z = k - 1`, `y = k`; in particular `-4`, `-3` for the negative control. -/
theorem twoAnchorBad_countermodel (m : Modality) (k : Int) (σ : State Gaps []) :
    ¬ holds σ (twoAnchorBad m k) := by
  change ¬ (∀ z y : Int, (some (decide (z < y)) : Option Bool) = some true →
    (some (decide (k < y)) : Option Bool) = some true)
  simpa only [Option.some.injEq, decide_eq_true_eq] using
    (show ¬ (∀ z y : Int, z < y → k < y) from fun h => by
      have hk : k < k := h (k - 1) k (by omega)
      omega)

/-- The original gap is valid: its hypothesis fails at `z = -1`, `y = 0`. -/
theorem gapKIntTwoAnchors_valid : Fml.Valid gapKIntTwoAnchors := by
  exact fun σ h => False.elim (twoAnchorBad_countermodel .box 0 σ h)

theorem gapKIntTwoAnchors_kencCovered : gapKIntTwoAnchors.kencCovered = true := by decide +kernel
theorem gapKIntTwoAnchors_covered : gapKIntTwoAnchors.Covered = true := by decide +kernel

/-- Exact verdict, certified through the existing soundness and coverage theorem. -/
theorem gapKIntTwoAnchors_verdict : decideLeaf gapKIntTwoAnchors = .proved :=
  (decideLeaf_proved_iff gapKIntTwoAnchors_covered).2 gapKIntTwoAnchors_valid

theorem gapKIntTwoAnchors_goal_verdict : decideGoal gapKIntTwoAnchors = .proved := by
  change decideLeaf gapKIntTwoAnchors = .proved
  exact gapKIntTwoAnchors_verdict

/-- The anchor/binder pipeline itself produces the improved verdict. -/
theorem gapKIntTwoAnchors_kenc_verdict : decideKEnc gapKIntTwoAnchors = .proved := by
  cases h : decideKEnc gapKIntTwoAnchors with
  | proved => rfl
  | refuted σ => exact False.elim ((decideKEnc_refutes h) (gapKIntTwoAnchors_valid σ))
  | unknown => exact False.elim ((decideKEnc_complete gapKIntTwoAnchors_kencCovered) h)

theorem twoAnchorGood_verdict (m : Modality) : decideLeaf (twoAnchorGood m (-3)) = .proved :=
  (decideLeaf_proved_iff (twoAnchorGood_covered m)).2 (twoAnchorGood_valid m (-3))

theorem twoAnchorBad_refuted (m : Modality) :
    ∃ σ, decideLeaf (twoAnchorBad m (-3)) = .refuted σ := by
  cases h : decideLeaf (twoAnchorBad m (-3)) with
  | proved =>
    exact False.elim ((twoAnchorBad_countermodel m (-3) (State.init Gaps))
      ((decideLeaf_sound h) (State.init Gaps)))
  | refuted σ => exact ⟨σ, rfl⟩
  | unknown => exact False.elim ((decideLeaf_complete (twoAnchorBad_covered m)) h)

/-- A true two-anchor universal in negative polarity must be refuted. -/
def twoAnchorNegative : Fml Gaps [] := .imp (twoAnchorGood .box (-3)) ff

theorem twoAnchorNegative_inTarget : twoAnchorNegative.inTarget {} = true := by decide +kernel
theorem twoAnchorNegative_kencCovered : twoAnchorNegative.kencCovered = true := by decide +kernel
theorem twoAnchorNegative_covered : twoAnchorNegative.Covered = true := by decide +kernel

theorem twoAnchorNegative_countermodel (σ : State Gaps []) : ¬ holds σ twoAnchorNegative := by
  intro h
  have hf := h (twoAnchorGood_valid .box (-3) σ)
  change (some (uintOfNat 0)) = some (uintOfNat 1) at hf
  exact (by decide +kernel : (some (uintOfNat 0)) ≠ some (uintOfNat 1)) hf

/-- All entry points retain the same typed countermodel. -/
theorem twoAnchorNegative_refuted :
    ∃ σ, decideKEnc twoAnchorNegative = .refuted σ ∧
      decideLeaf twoAnchorNegative = .refuted σ ∧
      decideGoal twoAnchorNegative = .refuted σ ∧ ¬ holds σ twoAnchorNegative := by
  cases h : decideKEnc twoAnchorNegative with
  | proved =>
    exact False.elim ((twoAnchorNegative_countermodel (State.init Gaps))
      ((decideKEnc_sound h) (State.init Gaps)))
  | refuted σ =>
    have hl : decideLeaf twoAnchorNegative = .refuted σ := by
      change decideKEnc twoAnchorNegative = .refuted σ
      exact h
    have hg : decideGoal twoAnchorNegative = .refuted σ := by
      change decideLeaf twoAnchorNegative = .refuted σ
      exact hl
    exact ⟨σ, rfl, hl, hg, twoAnchorNegative_countermodel σ⟩
  | unknown => exact False.elim ((decideKEnc_complete twoAnchorNegative_kencCovered) h)

/-- An unrelated local between the two integers must retain its position. -/
def twoAnchorDeep : Fml Gaps [.kint, .val .bool, .kint] :=
  .imp (zcmp .gt rfl zv (.pvZ (.there (.there .here)))) (zcmp .gt rfl zv (zlit (-3)))

theorem twoAnchorDeep_recognized :
    twoAnchorDeep.kintTwoAnchorView?.map (fun v => (v.index.toNat, v.threshold)) = some (1, -3) := by
  decide +kernel

/-- A Boolean false observation is not the supported truth literal. -/
def twoAnchorFalseTruth : Fml Gaps [.kint, .kint] :=
  .imp (.eq (.app2 (.zcmp .gt rfl) zv (.pvZ (.there .here))) (.app0 (.lit false)))
    (zcmp .gt rfl zv (zlit 0))

theorem twoAnchorFalseTruth_refused : twoAnchorFalseTruth.kintTwoAnchorView?.isSome = false := by
  decide +kernel

/-- Reading the outer integer on the left is not a read of the bound `y`. -/
def twoAnchorDifferentLocal : Fml Gaps [.kint, .kint] :=
  .imp (zcmp .gt rfl (.pvZ (.there .here)) (.pvZ (.there .here)))
    (zcmp .gt rfl zv (zlit 0))

theorem twoAnchorDifferentLocal_refused : twoAnchorDifferentLocal.kintTwoAnchorView?.isSome = false := by
  decide +kernel

/-- Symbolic multiplication remains outside the target and undecided. -/
def twoAnchorNonlinear : Fml Gaps [] :=
  .imp (bindZ "z" (bindZ "y"
    (.imp (zcmp .gt rfl (.app2 (.zbin .mul rfl) zv zv) (.pvZ (.there .here)))
      (zcmp .gt rfl zv (zlit 0))))) ff

theorem twoAnchorNonlinear_outside : twoAnchorNonlinear.inTarget {} = false := by decide +kernel
theorem twoAnchorNonlinear_not_encoded : twoAnchorNonlinear.kencB.2 = false := by decide +kernel
theorem twoAnchorNonlinear_unknown : decideGoal twoAnchorNonlinear = .unknown := by rfl

#print axioms twoAnchorGood_valid
#print axioms twoAnchorBad_countermodel
#print axioms gapKIntTwoAnchors_goal_verdict
#print axioms gapKIntTwoAnchors_verdict
#print axioms gapKIntTwoAnchors_kenc_verdict
#print axioms twoAnchorBad_refuted
#print axioms twoAnchorNegative_countermodel
#print axioms twoAnchorNegative_refuted

end Solidity.Examples.DecisionKInt
