import Solidity.Backend.Scalar.Wrapping

/-! Existing uint/int conversions are word reinterpretations, not checked
numeric casts. Narrow range guards and enum checks remain separate source
operations; this file does not silently strengthen explicit conversion guards. -/
namespace Solidity.Backend.Scalar

/-- Encoding a successfully range-checked intrinsic integer returns its word. -/
theorem encoded_int (n : Int) (h : PrimTy.int.inRange n = true) (tail : Stack) :
    (PrimTy.int.ofInt? n).map (fun v => encodeValue .int v :: tail) =
      some (BitVec.ofInt 256 n :: tail) := by
  simp only [PrimTy.ofInt?, h, dite_true, Option.map_some, encodeValue]

theorem encoded_uint (n : Int) (h : PrimTy.uint.inRange n = true) (tail : Stack) :
    (PrimTy.uint.ofInt? n).map (fun v => encodeValue .uint v :: tail) =
      some (BitVec.ofInt 256 n :: tail) := by
  simp only [PrimTy.ofInt?, h, dite_true, Option.map_some, encodeValue]

/-- Converting int256 to uint256 changes no stack bits. -/
def toUint : UnaryCertificate .toUint .int rfl where
  code := []
  correct := by
    intro a tail
    change some (BitVec.ofInt 256 a.val :: tail) =
      (PrimTy.uint.ofInt? (a.val % Semantics.uintBound)).map
        (fun v => encodeValue .uint v :: tail)
    exact (encoded_mod a.val tail).symm

/-- Subtracting one word modulus changes no bits. -/
theorem ofInt_sub_word (n : Int) :
    BitVec.ofInt 256 (n - Semantics.uintBound) = BitVec.ofInt 256 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, Semantics.uintBound, Int.sub_emod,
    Int.emod_self, Int.sub_zero, Int.emod_emod]

/-- Converting uint256 to int256 also changes no stack bits, even above 2^255. -/
def toInt : UnaryCertificate .toInt .uint rfl where
  code := []
  correct := by
    intro a tail
    let n : Int := if a.val < Semantics.intBound then a.val else a.val - Semantics.uintBound
    have hn : PrimTy.int.inRange n = true := by
      have ha := uint_range a
      unfold n Semantics.intBound Semantics.uintBound
      simp only [PrimTy.inRange, decide_eq_true_eq]
      split <;> omega
    change some (BitVec.ofInt 256 a.val :: tail) =
      (PrimTy.int.ofInt? n).map (fun v => encodeValue .int v :: tail)
    rw [encoded_int n hn]
    unfold n
    split
    · rfl
    · rw [ofInt_sub_word]

/-- Both representation-level casts compose to identity on every word. -/
theorem cast_code_chain (st : Stack) : run (toInt.code ++ toUint.code) st = some st := rfl

/-- Positive and negative boundary controls include a real intrinsic signed value. -/
example : UnOp.evalT .toInt (p := .uint) rfl ⟨255, by decide⟩ =
    some ⟨255, by decide⟩ := by rfl
example : run (toInt.code ++ toUint.code) [BitVec.ofInt 256 (-1), 99] =
    some [BitVec.ofInt 256 (-1), 99] := rfl

/-- info: 'Solidity.Backend.Scalar.toInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms toInt
/-- info: 'Solidity.Backend.Scalar.toUint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms toUint
/-- info: 'Solidity.Backend.Scalar.cast_code_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cast_code_chain

end Solidity.Backend.Scalar
