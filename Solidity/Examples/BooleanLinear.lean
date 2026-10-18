import Solidity.Calculus.DeclarationStaticReduction
import Solidity.Examples.ReadRealization

/-!
# Comparisons and partial Boolean expressions

Source comparisons keep checked arithmetic failure. Boolean expressions
short circuit in source order; logical negation of a formula differs from
negating a failed Boolean term. Every counterstate below falsifies its
original scoped formula.
-/

namespace Solidity.Examples.BooleanLinear

open Solidity.Decide Solidity.ReadRealization
open Solidity.Examples.ReadRealization (Bank three debt paused)
open scoped Solidity.Scoped

local instance : InContract := ⟨Bank⟩

def comparisonClaim : Fml Bank [] := dl!{ balances[3] <= 17 → balances[3] < 18 }
def comparisonReduction : StaticReduction comparisonClaim :=
  (checkedReduction? comparisonClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval comparisonReduction.verify.isLeft

def intervalClaim : Fml Bank [] := dl!{ balances[3] > 17 ∧ balances[3] < 19 → false }
def intervalReduction : StaticReduction intervalClaim :=
  (checkedReduction? intervalClaim).get (by decide +kernel)

/-- info: some 18 -/
#guard_msgs in
#eval match intervalReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def signedClaim : Fml Bank [] := dl!{ debt < 0 → debt <= 0 }
def signedReduction : StaticReduction signedClaim := (checkedReduction? signedClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval signedReduction.verify.isLeft

def signedFalse : Fml Bank [] := dl!{ debt >= 0 }
def signedFalseReduction : StaticReduction signedFalse := (checkedReduction? signedFalse).get (by decide +kernel)

/-- info: some true -/
#guard_msgs in
#eval match signedFalseReduction.verify with
  | .inl _ => none
  | .inr cm => some (decide ((debt.read cm.val.storage).val < 0))

def partialComparison : Fml Bank [] := dl!{ balances[3] - 1 < balances[3] }
def partialReduction : StaticReduction partialComparison :=
  (checkedReduction? partialComparison).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match partialReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def shortFalse : Fml Bank [] := dl!{ (false && (find(storage, balances[3]) - 1 == 0)) = false }
def shortFalseReduction : StaticReduction shortFalse := (checkedReduction? shortFalse).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval shortFalseReduction.verify.isLeft

def shortTrue : Fml Bank [] := dl!{ (true || (find(storage, balances[3]) - 1 == 0)) = true }
def shortTrueReduction : StaticReduction shortTrue := (checkedReduction? shortTrue).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval shortTrueReduction.verify.isLeft

def reversedFalse : Fml Bank [] := dl!{ ((find(storage, balances[3]) - 1 == 0) && false) = false }
def reversedFalseReduction : StaticReduction reversedFalse :=
  (checkedReduction? reversedFalse).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match reversedFalseReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def reversedTrue : Fml Bank [] := dl!{ ((find(storage, balances[3]) - 1 == 0) || true) = true }
def reversedTrueReduction : StaticReduction reversedTrue :=
  (checkedReduction? reversedTrue).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match reversedTrueReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def partialNot : Fml Bank [] := dl!{ !(find(storage, balances[3]) - 1 == 0) = !(find(storage, balances[3]) - 1 == 0) }
def partialNotReduction : StaticReduction partialNot := (checkedReduction? partialNot).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match partialNotReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def booleanCompare : Fml Bank [] := dl!{ paused != false → paused == true }
def booleanCompareReduction : StaticReduction booleanCompare :=
  (checkedReduction? booleanCompare).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval booleanCompareReduction.verify.isLeft

def booleanTermEq : Fml Bank [] := dl!{ (find(storage, paused) == true) = find(storage, paused) }
def booleanTermEqReduction : StaticReduction booleanTermEq :=
  (checkedReduction? booleanTermEq).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval booleanTermEqReduction.verify.isLeft

def strictEq : Fml Bank [] :=
  dl!{ (false == (find(storage, balances[3]) - 1 == 0)) = !(find(storage, balances[3]) - 1 == 0) }
def strictEqReduction : StaticReduction strictEq := (checkedReduction? strictEq).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match strictEqReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def declaredClaim : Fml Bank [] := .imp (declaration_facts[Bank]) intervalClaim
def declaredReduction : StaticReduction declaredClaim := declaration_checked_reduce[declaredClaim]

/-- info: some 18 -/
#guard_msgs in
#eval match declaredReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

/-- info: 'Solidity.Linear.CheckedBool.and_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Linear.CheckedBool.and_correct

/-- info: 'Solidity.Decide.StorageEncoding.boolEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms StorageEncoding.boolEq

end Solidity.Examples.BooleanLinear
