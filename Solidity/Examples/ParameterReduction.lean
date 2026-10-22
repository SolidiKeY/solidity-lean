import Solidity.Calculus.DeclarationStaticReduction
import Solidity.Examples.ReadRealization

/-!
# Guaranteed typed parameter counterinstances

The decision quantifies over every typed parameter value. Reconstructed
atoms identify a failing instance of the original universal formula;
storage is reconstructed alongside them when the body reads it.
-/

namespace Solidity.Examples.ParameterReduction

open Solidity.Decide Solidity.ReadRealization
open Solidity.Examples.ReadRealization (Bank three)
open scoped Solidity.Scoped

local instance : InContract := ⟨Bank⟩

def intervalClaim : Fml Bank [] := dl!{ ∀ uint x; x > 17 ∧ x < 19 → false }
def intervalReduction : ParameterReduction intervalClaim :=
  (parameterReduction? intervalClaim).get (by decide +kernel)

/-- info: some 18 -/
#guard_msgs in
#eval match intervalReduction.verify with
  | .inl _ => none
  | .inr cm => some (cm.atoms.get .uint 0).val

def intervalCountermodel : intervalReduction.Countermodel :=
  intervalReduction.countermodelOfCheck (⟨18, by decide +kernel⟩, ()) (by decide +kernel)

/-- The extracted value 18 also admits a cheap explicit source certificate. -/
theorem interval_invalid : ¬ Fml.Valid intervalClaim :=
  fun h => intervalCountermodel.refutes (h intervalCountermodel.state)

def signedClaim : Fml Bank [] := dl!{ ∀ int z; z < 0 → z <= 0 }
def signedReduction : ParameterReduction signedClaim :=
  (parameterReduction? signedClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval signedReduction.verify.isLeft

def booleanClaim : Fml Bank [] := dl!{ ∀ bool b; b == true → b != false }
def booleanReduction : ParameterReduction booleanClaim :=
  (parameterReduction? booleanClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval booleanReduction.verify.isLeft

def aliasClaim : Fml Bank [] := dl!{ ∀ uint x; x - x == 0 }
def aliasReduction : ParameterReduction aliasClaim := (parameterReduction? aliasClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval aliasReduction.verify.isLeft

def storageClaim : Fml Bank [] := dl!{ ∀ uint x; x == 17 ∧ balances[3] == 19 → false }
def storageReduction : ParameterReduction storageClaim :=
  (parameterReduction? storageClaim).get (by decide +kernel)

/-- info: some (17, 19) -/
#guard_msgs in
#eval match storageReduction.verify with
  | .inl _ => none
  | .inr cm => some ((cm.atoms.get .uint 0).val, (three.read cm.state.storage).val)

def dualClaim : Fml Bank [] :=
  dl!{ ∀ uint x; ∀ uint y; x == 17 ∧ y == 23 ∧ balances[3] == 19 → false }
def dualReduction : ParameterReduction dualClaim := (parameterReduction? dualClaim).get (by decide +kernel)

/-- info: some (17, 23, 19) -/
#guard_msgs in
#eval match dualReduction.verify with
  | .inl _ => none
  | .inr cm => some ((cm.atoms.get .uint 0).val, (cm.atoms.get .uint 1).val,
      (three.read cm.state.storage).val)

def mixedClaim : Fml Bank [] :=
  dl!{ ∀ bool b; ∀ int z; ∀ uint x; b == true ∧ z == (0 - 2) ∧ x == 17 → false }
def mixedReduction : ParameterReduction mixedClaim :=
  (parameterReduction? mixedClaim).get (by decide +kernel)

/-- info: some (true, -2, 17) -/
#guard_msgs in
#eval match mixedReduction.verify with
  | .inl _ => none
  | .inr cm => some (cm.atoms.get .bool 0, (cm.atoms.get .int 1).val, (cm.atoms.get .uint 2).val)

def updateClaim : Fml Bank [] := dl![.diamond]{ ∀ uint x; { y := x - 1 } y = y }
def updateReduction : ParameterReduction updateClaim :=
  (parameterReduction? updateClaim).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match updateReduction.verify with
  | .inl _ => none
  | .inr cm => some (cm.atoms.get .uint 0).val

def overflowClaim : Fml Bank [] := dl!{ ∀ uint x; x + 1 == x + 1 }
def overflowReduction : ParameterReduction overflowClaim :=
  (parameterReduction? overflowClaim).get (by decide +kernel)

-- KeY's `=` is reflexive: at the bound both sides overflow, and are equal.
/-- info: true -/
#guard_msgs in #eval overflowReduction.verify.isLeft

def signedUnderflow : Fml Bank [] := dl!{ ∀ int z; z - 1 == z - 1 }
def signedUnderflowReduction : ParameterReduction signedUnderflow :=
  (parameterReduction? signedUnderflow).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval signedUnderflowReduction.verify.isLeft

def declaredClaim : Fml Bank [] := .imp (declaration_facts[Bank]) storageClaim
def declaredReduction : ParameterReduction declaredClaim := declaration_parameter_reduce[declaredClaim]

/-- info: some (17, 19) -/
#guard_msgs in
#eval match declaredReduction.verify with
  | .inl _ => none
  | .inr cm => some ((cm.atoms.get .uint 0).val, (three.read cm.state.storage).val)

def underParameter : Fml Bank [] := dl!{ ∀ uint x;
  (∀ uint k; 0 <= balances[k] ∧ balances[k] <=
    115792089237316195423570985008687907853269984665640564039457584007913129639935)
    ∧ x == 17 ∧ balances[3] == 19 → false }
def underParameterReduction : ParameterReduction underParameter := declaration_parameter_reduce[underParameter]

/-- info: some (17, 19) -/
#guard_msgs in
#eval match underParameterReduction.verify with
  | .inl _ => none
  | .inr cm => some ((cm.atoms.get .uint 0).val, (three.read cm.state.storage).val)

def sameIndexParameters : List Parameter := [⟨.bool, 0⟩, ⟨.uint, 0⟩]
def sameIndexValues : Linear.ScalarCode.Values (Parameters.types sameIndexParameters [three]) :=
  (true, (⟨17, by decide +kernel⟩, (⟨19, by decide +kernel⟩, ())))
def sameIndexModel := Parameters.realize sameIndexParameters [three] sameIndexValues

/-- info: (true, 17, 19) -/
#guard_msgs in
#eval (sameIndexModel.2.get .bool 0, (sameIndexModel.2.get .uint 0).val,
  (three.read sameIndexModel.1).val)

example : (parameterReduction? (dl!{ ∀ uint x; balances[x] == 17 })).isNone = true := by decide +kernel

example : (parameterReduction? (dl!{ ∀ uint x; x == 17 → ∀ uint y; y == x })).isNone = true := by decide +kernel

/-- info: 'Solidity.Decide.ParameterReduction.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ParameterReduction.valid_iff

/-- info: 'Solidity.Decide.ParameterReduction.Countermodel.refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ParameterReduction.Countermodel.refutes

end Solidity.Examples.ParameterReduction
