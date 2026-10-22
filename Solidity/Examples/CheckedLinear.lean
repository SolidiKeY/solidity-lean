import Solidity.Calculus.DeclarationStaticReduction
import Solidity.Examples.ReadRealization

/-!
# Source arithmetic retains checked failure

These decisions and reconstructed stores use original scoped formulas.
Overflow, underflow, failure of a premise and failure of both sides of a
defined equality have distinct meanings, all retained by the translation.
-/

namespace Solidity.Examples.CheckedLinear

open Solidity.Decide Solidity.ReadRealization
open Solidity.Examples.ReadRealization (Bank three four debt)
open scoped Solidity.Scoped

local instance : InContract := ⟨Bank⟩

def arithmeticClaim : Fml Bank [] := dl!{ balances[3] == 17 → balances[3] + 1 == 17 }
def arithmeticReduction : StaticReduction arithmeticClaim :=
  (checkedReduction? arithmeticClaim).get (by decide +kernel)

/-- info: some 17 -/
#guard_msgs in
#eval match arithmeticReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def correctAddition : Fml Bank [] := dl!{ balances[3] == 17 → balances[3] + 1 == 18 }
def additionReduction : StaticReduction correctAddition :=
  (checkedReduction? correctAddition).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval additionReduction.verify.isLeft

def overflowClaim : Fml Bank [] := dl!{ balances[3] + 1 == balances[3] + 1 }
def overflowReduction : StaticReduction overflowClaim :=
  (checkedReduction? overflowClaim).get (by decide +kernel)

-- Two equally overflowing terms are equal: KeY's `=` is reflexive.
/-- info: true -/
#guard_msgs in #eval overflowReduction.verify.isLeft

def underflowClaim : Fml Bank [] := dl!{ balances[3] - 1 == balances[3] - 1 }
def underflowReduction : StaticReduction underflowClaim :=
  (checkedReduction? underflowClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval underflowReduction.verify.isLeft

def signedOverflowClaim : Fml Bank [] := dl!{ debt + 1 == debt + 1 }
def signedOverflowReduction : StaticReduction signedOverflowClaim :=
  (checkedReduction? signedOverflowClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval signedOverflowReduction.verify.isLeft

def signedUnderflowClaim : Fml Bank [] := dl!{ debt - 1 == debt - 1 }
def signedUnderflowReduction : StaticReduction signedUnderflowClaim :=
  (checkedReduction? signedUnderflowClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval signedUnderflowReduction.verify.isLeft

/-- Checked unsigned addition cannot wrap around to zero. An overflowing
premise is false, and therefore cannot refute this implication. -/
def noWrap : Fml Bank [] := dl!{ balances[3] + 1 == 0 → false }
def noWrapReduction : StaticReduction noWrap := (checkedReduction? noWrap).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval noWrapReduction.verify.isLeft

/-- The outer algebraic cancellation does not hide an inner failure. -/
def cancellation : Fml Bank [] := dl!{ balances[3] - 1 + 1 == balances[3] }
def cancellationReduction : StaticReduction cancellation :=
  (checkedReduction? cancellation).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match cancellationReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def overflowCancellation : Fml Bank [] := dl!{ balances[3] + 1 - 1 == balances[3] }
def overflowCancellationReduction : StaticReduction overflowCancellation :=
  (checkedReduction? overflowCancellation).get (by decide +kernel)

/-- info: some true -/
#guard_msgs in
#eval match overflowCancellationReduction.verify with
  | .inl _ => none
  | .inr cm => some (decide ((three.read cm.val.storage).val = ((2 ^ 256 : Nat) : Int) - 1))

def closedFailure : Fml Bank [] := dl!{ 0 - 1 == 0 - 1 }
def closedFailureReduction : StaticReduction closedFailure :=
  (checkedReduction? closedFailure).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval closedFailureReduction.verify.isLeft

/-- Two identically failed closed computations are equal: KeY's `=` reads
both sides in the Theory, where they halt alike. -/
theorem closedFailure_valid : Fml.Valid closedFailure := fun _ => rfl

def declaredClaim : Fml Bank [] := .imp (declaration_facts[Bank]) arithmeticClaim
def declaredReduction : StaticReduction declaredClaim := declaration_checked_reduce[declaredClaim]

/-- info: some 17 -/
#guard_msgs in
#eval match declaredReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def signedClaim : Fml Bank [] := dl!{ debt + 2 == 0 → debt == (0 - 2) }
def signedReduction : StaticReduction signedClaim := (checkedReduction? signedClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval signedReduction.verify.isLeft

example : True := by
  fail_if_success
    have _ : StaticReduction (dl!{ (∀ uint k; balances[k] == 1) → balances[3] == 0 }) :=
      declaration_checked_reduce[dl!{ (∀ uint k; balances[k] == 1) → balances[3] == 0 }]
  trivial

example : (checkedReduction? (dl!{ balances[balances[3]] == 7 })).isNone = true := by decide +kernel
example : (checkedReduction? (dl!{ [balances[3] = 7;] balances[3] == 7 })).isNone = true := by decide +kernel

/-- info: 'Solidity.Linear.CheckedScalar.arith_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Linear.CheckedScalar.arith_correct

end Solidity.Examples.CheckedLinear
