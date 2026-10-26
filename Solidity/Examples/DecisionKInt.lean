import Solidity.Examples.Decision

/-!
# Binders of KeY's `int` over two words (M7, feature 30)

`decideKEnc` (`Calculus/Decision.lean`, `Calculus/KIntEncode.lean`) reads a
binder of KeY's `int` whose comparisons read it against bounded terms over
two words, at every state.  The former counterexample `gapKIntNeg`, a
negative binder (an `∃` over `ℤ`), is proved, its false variant refuted;
a positive binder in a leaf reading the ledger elsewhere (outside feature
26, which needs the ledger free) is proved and refuted.  Coverage is the
kernel's, the verdicts the compiled ones (each is a few binary derivatives
over word codes).  Two shapes stay counterexamples: a binder compared with
an unbounded term at another coefficient (a ledger entry, `gapKIntNet`),
and two binders compared with each other under a negation
(`gapKIntNested`).
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

/-- Counterexamples still: a binder compared with a ledger entry,
`∀ int z. net(0) == z → net(0) + 1 > z` (the remainder `net(0)` unbounded),
and two binders compared under a negation, `(∀ int z. ∀ int y. y > z) → 0 == 1`. -/
def gapKIntNet : Fml Gaps [] :=
  bindZ "z" (.imp (zcmp .eqB rfl net0 zv) (zcmp .gt rfl (zplus net0 (zlit 1)) zv))
def gapKIntNested : Fml Gaps [] :=
  .imp (bindZ "z" (bindZ "y" (zcmp .gt rfl zv (.pvZ (.there .here))))) ff

theorem kintNegBad_inTarget : kintNegBad.inTarget {} = true := by decide +kernel
theorem kintNetElse_inTarget : kintNetElse.inTarget {} = true := by decide +kernel
theorem gapKIntNet_inTarget : gapKIntNet.inTarget {} = true := by decide +kernel
theorem gapKIntNested_inTarget : gapKIntNested.inTarget {} = true := by decide +kernel

theorem gapKIntNeg_covered : gapKIntNeg.Covered = true := by decide +kernel
theorem kintNegBad_covered : kintNegBad.Covered = true := by decide +kernel
theorem kintNetElse_covered : kintNetElse.Covered = true := by decide +kernel
theorem kintNetElseBad_covered : kintNetElseBad.Covered = true := by decide +kernel

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

/-- info: ["proved", "refuted", "proved", "refuted", "proved"] -/
#guard_msgs in
#eval [gapKIntNeg, kintNegBad, kintNetElse, kintNetElseBad, kintNegWord].map verdict

/-- info: ["unknown", "unknown"] -/
#guard_msgs in
#eval [gapKIntNet, gapKIntNested].map verdict

end Solidity.Examples.DecisionKInt
