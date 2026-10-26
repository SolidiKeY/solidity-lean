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
below, not evaluated in the build.  Two shapes stay
counterexamples: a binder compared with two unbounded terms
(`gapKIntTwoAnchors`, `∀ y. y > z → y > 0` under a negation: real
Presburger alternation over `ℤ`), and a negative quantifier in a leaf that
reads the ledger (`gapQuantLedger`, `(∀ uint y. y > 0) → net(0) > 0`: no
pipeline takes both, whatever the binder's type).
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

/-- Counterexamples still: a binder compared with two unbounded terms (`z`
and the threshold `0` past the anchor `z`), and a negative quantifier
(here of `uint`) in a leaf that reads the ledger. -/
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
pins: coverage by the kernel, so `decideLeaf` answers, and exactly. -/

theorem kintNegBad_answers : decideLeaf kintNegBad ≠ .unknown := decideLeaf_complete kintNegBad_covered
theorem kintNetElseBad_answers : decideLeaf kintNetElseBad ≠ .unknown :=
  decideLeaf_complete kintNetElseBad_covered
theorem kintNetBad_answers : decideLeaf kintNetBad ≠ .unknown := decideLeaf_complete kintNetBad_covered
theorem kintNestedBad_answers : decideLeaf kintNestedBad ≠ .unknown :=
  decideLeaf_complete kintNestedBad_covered

end Solidity.Examples.DecisionKInt
