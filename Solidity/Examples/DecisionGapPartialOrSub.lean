import Solidity.Calculus.Decision
import Solidity.Calculus.DecisionPartialOrSubComplete
import Solidity.Calculus.Surface

/-!
# Standalone subtraction-literal family controls (proposed S2)

Source recognition, validity and explicit countermodels are checked before
public-dispatcher integration. The preserved public verdict/coverage controls
remain binding and are deferred until their production dependencies land.
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

/-- Members and the non-member control. -/
theorem members : good.partialOrSub = true ∧ atZero.partialOrSub = true ∧
    wrongValue.partialOrSub = true ∧ otherClaim.partialOrSub = false := by
  refine ⟨(partialOrSub_iff).mpr ?_, (partialOrSub_iff).mpr ?_,
    (partialOrSub_iff).mpr ?_, by decide +kernel⟩
  · exact ⟨⟨roots, uintOfNat 3, uintOfNat 5, uintOfNat 2, uintOfNat 5,
      by decide +kernel, .user "i", .user "j", rfl⟩⟩
  · exact ⟨⟨roots, uintOfNat 3, uintOfNat 5, uintOfNat 0, uintOfNat 5,
      by decide +kernel, .user "i", .user "j", rfl⟩⟩
  · exact ⟨⟨roots, uintOfNat 7, uintOfNat 5, uintOfNat 4, uintOfNat 6,
      by decide +kernel, .user "i", .user "j", rfl⟩⟩

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

/-- Every recognized example has a certified family answer, before public integration. -/
theorem family_answers : (partialOrSubAnswer? good).isSome = true ∧
    (partialOrSubAnswer? atZero).isSome = true ∧
    (partialOrSubAnswer? wrongValue).isSome = true :=
  ⟨partialOrSubAnswer_isSome members.1, partialOrSubAnswer_isSome members.2.1,
    partialOrSubAnswer_isSome members.2.2.1⟩

end Solidity.Examples.DecisionGapPartialOrSub
