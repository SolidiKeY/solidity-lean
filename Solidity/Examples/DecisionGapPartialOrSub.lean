import Solidity.Calculus.Decision
import Solidity.Calculus.Surface

/-!
# Partial-OR floor at any halting subtraction literal: both polarities

`((i ≤ j && i < cap - 3) || i ≤ i) == true → owed[i] == 5` blocks: valid at a
positive key with value `5`, refuted at key zero and at a wrong value, decided
by `Calculus/DecisionPartialOrSub.lean` with the region countermodel. A guard
whose right disjunct is not `i ≤ i` (`j ≤ i`) is not a member and stays an
in-target unknown: the narrowed Residue shape of partial APF guards.
-/
namespace Solidity.Examples.DecisionGapPartialOrSub
open Solidity.Decide Solidity.Decide.ResidueReason
set_option Elab.async false

/-- One `uint ⇒ uint` mapping root and one uint root. -/
def Floors : Contract := contract!{ mapping(uint => uint) owed; uint cap; }

/-- The family's roots in `Floors`. -/
def roots : PartialOrRoots Floors := ⟨"cap", "owed", rfl, rfl⟩

/-- `owed[k] == r` under the block `owed[i] == v`, subtraction literal `c`. -/
def claim (c v k r : Nat) : Fml Floors [] :=
  roots.subClaim (.user "i") (.user "j") (uintOfNat c) (uintOfNat v) (uintOfNat k) (uintOfNat r)

/-- Valid: positive key, the block's value. -/
def good : Fml Floors [] := claim 3 5 2 5
/-- Refuted: key zero is unconstrained when `cap < 3`. -/
def atZero : Fml Floors [] := claim 3 5 0 5
/-- Refuted: a wrong value. -/
def wrongValue : Fml Floors [] := claim 7 5 4 6

/-- The right disjunct `j ≤ i` instead of `i ≤ i`: not a member. Written with
constructors, as `dl{}` cannot spell a `&&` under `||` in a guard. -/
def otherGuard : Tm Floors [.val .uint, .val .uint] (.val .bool) :=
  .app2 (.binop .or rfl)
    (.app2 (.binop .and rfl)
      (.app2 (.binop .le (p := .uint) rfl) (.pvV (.there .here)) (.pvV .here))
      (.app2 (.binop .lt (p := .uint) rfl) (.pvV (.there .here))
        (.app2 (.binop .sub rfl) roots.scalarRead (.app0 (.lit (uintOfNat 3))))))
    (.app2 (.binop .le (p := .uint) rfl) (.pvV .here) (.pvV (.there .here)))
/-- The block over `otherGuard`, claim at key `2`. -/
def otherClaim : Fml Floors [] :=
  .imp (.all (.user "i") .uint (.all (.user "j") .uint
    (.imp (.eq otherGuard (.app0 (.lit true)))
      (.eq (roots.mapRead (.pvV (.there .here))) (.app0 (.lit (uintOfNat 5)))))))
    (.eq (roots.mapRead (.app0 (.lit (uintOfNat 2)))) (.app0 (.lit (uintOfNat 5))))

/-- Target, membership, coverage and the public verdict. -/
@[noinline] def observe (φ : Fml Floors []) : Bool × Bool × Bool × String :=
  (φ.inTarget {}, φ.partialOrSub, φ.Covered, match decideGoal φ with
    | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")

/--
info: [(true, true, true, "proved"), (true, true, true, "refuted"), (true, true, true, "refuted"),
  (true, false, false, "unknown")]
-/
#guard_msgs in #eval [good, atZero, wrongValue, otherClaim].map observe

/-- Members and the non-member control. -/
theorem members : good.partialOrSub = true ∧ atZero.partialOrSub = true ∧
    wrongValue.partialOrSub = true ∧ otherClaim.partialOrSub = false := by decide +kernel

/-- The three members are in the target and covered. -/
theorem covered : good.inTarget {} = true ∧ good.Covered = true ∧ atZero.Covered = true ∧
    wrongValue.Covered = true := by decide +kernel

/-- The narrowed Residue control: in the target, not covered. -/
theorem other_residue : otherClaim.inTarget {} = true ∧ otherClaim.Covered = false := by
  decide +kernel

/-- The region state refutes key zero, independently of the decider. -/
theorem atZero_countermodel :
    ¬ holds (roots.counterState (uintOfNat 5) (uintOfNat 5)) atZero :=
  roots.subClaim_counter_refutes _ _ _ (by decide) _ _ _ (by decide)

/-- The region state refutes the wrong value. -/
theorem wrongValue_countermodel :
    ¬ holds (roots.counterState (uintOfNat 5) (uintOfNat 6)) wrongValue :=
  roots.subClaim_counter_refutes _ _ _ (by decide) _ _ _ (by decide)

/-- The positive member, by the family's semantics. -/
theorem good_valid : Fml.Valid good :=
  roots.subClaim_positive_valid _ _ _ _ _ (by decide)

/-- The decider proves the positive member. -/
theorem good_proved : decideGoal good = .proved := by
  have hd : decideGoal good ≠ .unknown := decideGoal_complete covered.2.1 rfl
  cases he : decideGoal good with
  | proved => rfl
  | refuted σ => exact absurd ((Fml.holdsH_iff σ good rfl).mpr (good_valid σ)) (decideGoal_refutes he)
  | unknown => exact absurd he hd

/-- info: 'Solidity.Examples.DecisionGapPartialOrSub.good_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms good_proved

end Solidity.Examples.DecisionGapPartialOrSub
