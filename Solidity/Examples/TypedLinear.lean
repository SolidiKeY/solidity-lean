import Solidity.Calculus.TypedLinear
import Solidity.Calculus.LinearSyntax

/-!
# Exact bounded arithmetic and typed counterassignments

The arithmetic notation refers to scalar codes. A signed code `0` is the
minimum signed word, not the signed number zero. No source-term translation
is claimed here.
-/

namespace Solidity.Examples.TypedLinear

open Solidity.Linear ScalarCode

example : decode .bool ⟨0, by decide⟩ = false := rfl
example : decode .bool ⟨1, by decide⟩ = true := rfl
example : decode? .bool 2 = none := rfl
example : decode? .uint (2 ^ 256) = none := by decide +kernel
example : decode? .int (2 ^ 256) = none := by decide +kernel

example : (decode .uint ⟨0, by decide⟩).val = 0 := rfl
example : (decode .uint ⟨2 ^ 256 - 1, by decide +kernel⟩).val = (2 ^ 256 : Nat) - 1 := by decide +kernel
example : (decode .int ⟨0, by decide +kernel⟩).val = -((2 ^ 255 : Nat) : Int) := rfl
example : (decode .int ⟨2 ^ 256 - 1, by decide +kernel⟩).val = ((2 ^ 255 : Nat) : Int) - 1 := by decide +kernel

def minusTwo : PrimTy.int.Denote := ⟨-2, by decide +kernel⟩
example : decode? .int (encode .int minusTwo).val = some minusTwo := decode?_encode _ _

def boolDomain : TypedFormula [.bool] := ⟨linear!{ [1] ≤ 1 }, by decide⟩
def boolClaim : TypedFormula [.bool] := ⟨linear!{ ¬([1] = 1) }, by decide⟩

example : boolDomain.guarded.decide = true := by decide +kernel
example : boolDomain.Valid := boolDomain.valid_iff.mpr ((AFml.decide_iff _).1 (by decide +kernel))
example : boolDomain.verify.isLeft = true := by decide +kernel

def boolModel := boolClaim.countermodel (by decide +kernel)
example : boolModel.val.1 = true := by decide +kernel
example : boolClaim.verify.isRight = true := by decide +kernel

/-- The domain constraint does not permit the spurious Boolean code `2`. -/
def boolCannotBeTwo : TypedFormula [.bool] := ⟨linear!{ ¬([1] = 2) }, by decide⟩
example : boolCannotBeTwo.guarded.decide = true := by decide +kernel

def uintClaim : TypedFormula [.uint] := ⟨linear!{ ¬([1] = 17) }, by decide⟩

/-- info: some 17 -/
#guard_msgs in
#eval match uintClaim.verify with
  | .inl _ => none
  | .inr cm => some cm.val.1.val

def mixedClaim : TypedFormula [.bool, .int, .uint] :=
  ⟨.not (.and (linear!{ [1] = 1 })
    (.and (.eq [0, 1] (((2 ^ 255 : Nat) : Int) - 2)) (linear!{ [0, 0, 1] = 17 }))), by decide⟩

/-- info: some (true, -2, 17) -/
#guard_msgs in
#eval match mixedClaim.verify with
  | .inl _ => none
  | .inr cm => some (cm.val.1, cm.val.2.1.val, cm.val.2.2.1.val)

/-- info: 'Solidity.Linear.TypedFormula.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TypedFormula.valid_iff

/-- info: 'Solidity.Linear.TypedFormula.verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TypedFormula.verify

end Solidity.Examples.TypedLinear
