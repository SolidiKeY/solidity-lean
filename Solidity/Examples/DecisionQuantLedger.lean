import Solidity.Examples.DecisionKInt

/-!
# Negative scalar quantifiers beside ledger observations

The original gap is unchanged. Controls use a true quantified premise so
ledger equality, address aliases and payment updates determine the answer.
-/

namespace Solidity.Examples.DecisionQuantLedger

open Solidity.Decide Solidity.Examples.Decision Solidity.Examples.DecisionKInt
open scoped Solidity.Scoped
local instance : InContract := ⟨Gaps⟩

/-- True antecedent, false at the zero ledger. -/
def bad : Fml Gaps [] := dl!{ (∀ uint y; y >= 0) → net(0) > 0 }
/-- Equal addresses observe one entry. -/
def aliasOk : Fml Gaps [] :=
  dl!{ ∀ uint a; ∀ uint b; (∀ uint y; y >= 0) → a == b → net(a) = net(b) }
/-- Equal addresses cannot have strictly ordered entries. -/
def aliasBad : Fml Gaps [] :=
  dl!{ ∀ uint a; ∀ uint b; (∀ uint y; y >= 0) → a == b → net(a) > net(b) }
/-- Distinct addresses may carry different ledger entries. -/
def distinctBad : Fml Gaps [] :=
  dl!{ ∀ uint a; ∀ uint b; (∀ uint y; y >= 0) → a != b → net(a) = net(b) }
/-- Existing successful payment control beneath a negative quantifier. -/
def paymentOk : Fml Gaps [] :=
  dl!{ ∀ uint a; (∀ uint y; y >= 0) → net(a) >= 1 → {pay(a, 1)} net(a) >= 0 }
/-- Payment can make an arbitrary receiver entry negative. -/
def paymentBad : Fml Gaps [] :=
  dl!{ ∀ uint a; (∀ uint y; y >= 0) → {pay(a, 1)} net(a) >= 0 }
/-- Ledger entries are not bounded by a primitive word. -/
def highOk : Fml Gaps [] :=
  dl!{ (∀ uint y; y >= 0) → net(0) = 115792089237316195423570985008687907853269984665640564039457584007913129639953 →
    net(0) > 115792089237316195423570985008687907853269984665640564039457584007913129639936 }

/-- A refutation requires a ledger entry above the primitive-word range. -/
def highBad : Fml Gaps [] :=
  dl!{ (∀ uint y; y >= 0) → net(0) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935 }
/-- A refutation requires a negative ledger entry. -/
def negativeBad : Fml Gaps [] := dl!{ (∀ uint y; y >= 0) → net(0) >= 0 }

/-- A genuinely nonclosed quantified subformula sharing its parameter with
an address: y=0 falsifies the antecedent at every uint x. -/
def paramOk : Fml Gaps [] := dl!{ ∀ uint x; (∀ uint y; y > x) → net(x) > 0 }
/-- At x=0 the quantified premise holds and the ledger consequence may fail. -/
def paramBad : Fml Gaps [] := dl!{ ∀ uint x; (∀ uint y; y >= x) → net(x) > 0 }

/-- The unchanged original statement has a certified reduction. -/
theorem original_covered : gapQuantLedger.Covered = true := by decide +kernel
/-- Zero is a typed counterexample to the original universally quantified
antecedent, independently of every ledger observation. -/
theorem original_valid : Fml.Valid gapQuantLedger := by
  intro σ h
  have hy : (some false : Option Bool) = some true := h (uintOfNat 0)
  cases hy
/-- The exact verdict of the original pin, proved in the kernel. -/
theorem original_proved : decideLeaf gapQuantLedger = .proved :=
  (decideLeaf_proved_iff original_covered).2 original_valid

/-- The public goal pipeline has the same exact verdict, without a hash. -/
theorem original_goal_proved : decideGoal gapQuantLedger = .proved := by
  have hh : gapQuantLedger.hasHash = false := by decide +kernel
  unfold decideGoal
  rw [hh, if_neg Bool.false_ne_true]
  exact original_proved

/-- Positive and negative controls are recognized with certificates. -/
theorem controls_covered :
    [bad, aliasOk, aliasBad, distinctBad, paymentOk, paymentBad, highOk, highBad, negativeBad,
      paramOk, paramBad].all Fml.quantLedgerCovered = true := by decide +kernel

/-- Nonclosed definitions retain their free typed parameter and cannot use
the closed-arithmetic route. Both cases exercise the generic quantified path. -/
theorem parameters_use_generic :
    [paramOk, paramBad].map (fun φ => (quantLedgerReduction? φ).map fun r =>
      (r.body.Qs.map (fun e => e.2.freeParams.length),
        (ReadFormula.ofFormula? (closeLedgerQuantifiers r.prep.body.ledgerCut).formula).isSome)) =
      [some ([1], false), some ([1], false)] := by decide +kernel

/-- Distinct natural-code pairs denote the same negative ledger entry. -/
theorem shifted_codes :
    (ledgerOfCodes (fun k => if k = 0 then 0 else 1) 0 [uintOfNat 0] 0).entries =
    (ledgerOfCodes (fun k => if k = 0 then 3 else 4) 0 [uintOfNat 0] 0).entries := by decide +kernel
/-- The code representation realizes an amount strictly above a uint word. -/
theorem unbounded_codes :
    (ledgerOfCodes (fun k => if k = 0 then 2^256 else 0) 0 [uintOfNat 0] 0).entries =
      [(0, (2^256 : Int))] := by decide +kernel

/-- info: 'Solidity.Examples.DecisionQuantLedger.original_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms original_proved
#print axioms parameters_use_generic
#print axioms original_goal_proved
/-- info: 'Solidity.Examples.DecisionQuantLedger.shifted_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms shifted_codes
/-- info: 'Solidity.Examples.DecisionQuantLedger.unbounded_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unbounded_codes

end Solidity.Examples.DecisionQuantLedger
