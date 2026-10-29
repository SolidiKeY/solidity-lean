import Solidity.Examples.MemoryNegativeCountermodel
import Solidity.Calculus.FunContract

/-!
# The original negative memory block: exact closer refutation

The original definition and target certificate are unchanged. The native
closer is executed on it, and its exact returned verdict is kernel-certified
using proved coverage, the original countermodel, and closer soundness and
completeness. No binary-derivative search is repeated in the kernel.
-/

namespace Solidity.Examples.MemoryNegativeDecision

open Solidity.Decide Solidity.Examples.Decision
open Solidity.Examples.MemoryNegativeCountermodel

set_option Elab.async false

/-- Coverage reduces the actual production preparation and parser in the kernel. -/
theorem gap_memCovered : gapMemInnerNeg.memCovered = true := by
  decide +kernel

-- The compiled production coverage check agrees with the kernel reduction above.
#guard gapMemInnerNeg.memCovered

private abbrev exterior : MxExterior .uint :=
  .eq (.read (uintOfNat 0)) (.lit .uint (uintOfNat 0))

theorem gap_covered : gapMemInnerNeg.Covered = true := by
  simp only [Fml.Covered, gap_memCovered, Bool.or_true, Bool.true_or]

/-- This is about the actual original decision function and its returned
state, not the separately constructed empty-array witness. -/
theorem gap_decision : ∃ σ, decideGoal gapMemInnerNeg = .refuted σ := by
  have hu : decideLeaf gapMemInnerNeg ≠ .unknown := decideLeaf_complete gap_covered
  cases he : decideLeaf gapMemInnerNeg with
  | proved => exact False.elim (gapMemInnerNeg_notValid (decideLeaf_sound he))
  | unknown => exact False.elim (hu he)
  | refuted σ =>
    refine ⟨σ, ?_⟩
    change (if gapMemInnerNeg.hasHash then decideHash gapMemInnerNeg else decideLeaf gapMemInnerNeg) = _
    rw [if_neg (by decide +kernel)]
    exact he

theorem gap_returned_countermodel :
    ∃ σ, decideGoal gapMemInnerNeg = .refuted σ ∧ ¬ Fml.holdsH σ gapMemInnerNeg := by
  obtain ⟨σ, hσ⟩ := gap_decision
  exact ⟨σ, hσ, decideGoal_refutes hσ⟩

theorem gap_verdict : verdict gapMemInnerNeg = "refuted" := by
  obtain ⟨σ, hσ⟩ := gap_decision
  simp only [verdict, hσ]

/-- info: "refuted" -/
#guard_msgs in #eval verdict gapMemInnerNeg

/-- A live read implied by the uniform range block: the empty array is
vacuous on both the block and the consequent's length guard. -/
def guardedZero : Fml Gaps [] := cdl[Gaps]{ ∀ fresh uint[] s; (∀ uint i; ‹mxRangeBody .here (uintOfNat 0)›) → ‹mxRangeInstance .here (uintOfNat 0) (litU 0)› }

example : guardedZero =
  .allocAll (.user "s") UA
  (.imp (.all (.user "i") .uint (mxRangeBody .here (uintOfNat 0)))
    (mxRangeInstance .here (uintOfNat 0) (litU 0))) := rfl

def guardedWrong : Fml Gaps [] := cdl[Gaps]{ ∀ fresh uint[] s; (∀ uint i; ‹mxRangeBody .here (uintOfNat 0)›) → ‹mxRangeInstance .here (uintOfNat 1) (litU 0)› }

example : guardedWrong =
  .allocAll (.user "s") UA
  (.imp (.all (.user "i") .uint (mxRangeBody .here (uintOfNat 0)))
    (mxRangeInstance .here (uintOfNat 1) (litU 0))) := rfl

/-- Theory equality retains equal halted reads. -/
def haltedEqual : Fml Gaps [] := cdl[Gaps]{ ∀ fresh uint[] s; (∀ uint i; ‹mxRangeBody .here (uintOfNat 0)›) → s[0] = s[0] }

example : haltedEqual =
  .allocAll (.user "s") UA
  (.imp (.all (.user "i") .uint (mxRangeBody .here (uintOfNat 0)))
    (.eq (mrdG .dyn .here (litU 0)) (mrdG .dyn .here (litU 0)))) := rfl

/-- A program comparison still fails when both reads halt. -/
def haltedCompare : Fml Gaps [] := cdl[Gaps]{ ∀ fresh uint[] s; (∀ uint i; ‹mxRangeBody .here (uintOfNat 0)›) → (s[0] == s[0]) = true }

example : haltedCompare =
  .allocAll (.user "s") UA
  (.imp (.all (.user "i") .uint (mxRangeBody .here (uintOfNat 0)))
    (isT (eqB (mrdG .dyn .here (litU 0)) (mrdG .dyn .here (litU 0))))) := rfl

def boolGuarded (v : Bool) : Fml Gaps [] :=
  cdl[Gaps]{ ∀ fresh bool[] s;
    (∀ uint i; ‹mxRangeBody .here true›) → ‹mxRangeInstance .here v (litU 0)› }

example (v : Bool) : boolGuarded v =
  .allocAll (.user "s") (.array (.prim .bool))
    (.imp (.all (.user "i") .uint (mxRangeBody .here true))
      (mxRangeInstance .here v (litU 0))) := rfl

theorem guardedZero_valid : Fml.Valid guardedZero := by
  intro σ o h
  exact (mxInst_holds (mxRangeBody_inst (.user "i") .here (uintOfNat 0) (litU 0))
    (σ.allocPush o) rfl).2 (h (uintOfNat 0))

theorem haltedEqual_valid : Fml.Valid haltedEqual := by
  intro σ o _
  rfl

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in
#eval [verdict guardedZero, verdict guardedWrong, verdict haltedEqual,
  verdict haltedCompare, verdict (boolGuarded true), verdict (boolGuarded false)]

/-- Scope refusals remain fallbacks rather than unsupported rewrites. -/
def parentRead : Fml Gaps [.val .uint] := cdlIn[Gaps | uint x]{ ∀ fresh uint[] s; (∀ uint i; ‹mxRangeBody .here (uintOfNat 0)›) → s[x] = 0 }

example : parentRead =
  .allocAll (.user "s") UA
  (.imp (.all (.user "i") .uint (mxRangeBody .here (uintOfNat 0)))
    (.eq (mrdG .dyn .here (.pvV (.there .here))) (litU 0))) := rfl

def otherArrayRead : Fml Gaps [.mem UA] := cdlIn[Gaps | uint[] memory t]{ ∀ fresh uint[] s; (∀ uint i; ‹mxRangeBody .here (uintOfNat 0)›) → t[0] = 0 }

example : otherArrayRead =
  .allocAll (.user "s") UA
  (.imp (.all (.user "i") .uint (mxRangeBody .here (uintOfNat 0)))
    (.eq (mrdG .dyn (.there .here) (litU 0)) (litU 0))) := rfl

def lengthIndexed : Fml Gaps [] := cdl[Gaps]{ ∀ fresh uint[] s; (∀ uint i; ‹mxRangeBody .here (uintOfNat 0)›) → s[s.length] = 0 }

example : lengthIndexed =
  .allocAll (.user "s") UA
  (.imp (.all (.user "i") .uint (mxRangeBody .here (uintOfNat 0)))
    (.eq (mrdG .dyn .here (mlenG .here)) (litU 0))) := rfl

#guard !(mxNegativePrepare parentRead).changed
#guard !(mxNegativePrepare otherArrayRead).changed
#guard !(mxNegativePrepare lengthIndexed).changed
#guard (mxNegativePrepare gapMemInnerNeg).changed

/-- A preserved prefix and array name reserve their indices before the new
length atom is chosen. No parser-specific fresh-name family is introduced. -/
def namedPrefix : Fml Gaps [] := cdl[Gaps]{ ∀ uint se41;
    ‹mxNegativeSource (.fresh "se" 9) (.user "i") (uintOfNat 0) exterior› }

example : namedPrefix =
  .all (.fresh "se" 41) .uint
  (mxNegativeSource (.fresh "se" 9) (.user "i") (uintOfNat 0) exterior) := rfl

#guard (mxNegativePrepare namedPrefix).changed
#guard match (mxNegativePrepare namedPrefix).body with
  | .all _ _ (.all x _ _) => x == .fresh "se" namedPrefix.fresh && namedPrefix.fresh > 41
  | _ => false

/-- An exterior value binder is refused instead of being interpreted in the
fresh array's context. The prefix case above is a separate supported shape. -/
def nestedExterior : Fml Gaps [] := cdl[Gaps]{ ∀ fresh uint[] s; (∀ uint i; ‹mxRangeBody .here (uintOfNat 0)›) → ∀ uint j; j = j }

example : nestedExterior =
  .allocAll (.user "s") UA
  (.imp (.all (.user "i") .uint (mxRangeBody .here (uintOfNat 0)))
    (.all (.user "j") .uint (.eq (.pvV .here) (.pvV .here)))) := rfl

#guard !(mxNegativePrepare nestedExterior).changed

#print axioms gap_memCovered
#print axioms gap_decision
#print axioms gap_returned_countermodel
#print axioms guardedZero_valid
#print axioms haltedEqual_valid

end Solidity.Examples.MemoryNegativeDecision
