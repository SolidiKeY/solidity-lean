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
      have ha : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a
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

/-- Source cast round trip at `uint256`, not just identity of emitted code. -/
theorem cast_roundtrip_uint (a : PrimTy.uint.Denote) :
    (UnOp.evalT .toInt (p := .uint) rfl a).bind
      (fun b => UnOp.evalT .toUint (p := .int) rfl b) = some a := by
  have h1 : some [encodeValue .uint a] =
      (UnOp.evalT .toInt (p := .uint) rfl a).map (fun b => [encodeValue .int b]) :=
    toInt.correct a []
  change some [encodeValue .uint a] =
    (UnOp.evalT .toInt (p := .uint) rfl a).map (fun b => [encodeValue .int b]) at h1
  cases hx : UnOp.evalT .toInt (p := .uint) rfl a with
  | none => simp only [hx, Option.map_none, reduceCtorEq] at h1
  | some b =>
    simp only [hx, Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at h1
    have h2 : some [encodeValue .int b] =
        (UnOp.evalT .toUint (p := .int) rfl b).map (fun c => [encodeValue .uint c]) :=
      toUint.correct b []
    change some [encodeValue .int b] =
      (UnOp.evalT .toUint (p := .int) rfl b).map (fun c => [encodeValue .uint c]) at h2
    cases hy : UnOp.evalT .toUint (p := .int) rfl b with
    | none => simp only [hy, Option.map_none, reduceCtorEq] at h2
    | some c =>
      simp only [hy, Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at h2
      have hc : c = a := encode_uint_injective (h2.symm.trans h1.symm)
      simp only [hy, Option.bind_some, hc]

/-- Source cast round trip at `int256`, not just identity of emitted code. -/
theorem cast_roundtrip_int (a : PrimTy.int.Denote) :
    (UnOp.evalT .toUint (p := .int) rfl a).bind
      (fun b => UnOp.evalT .toInt (p := .uint) rfl b) = some a := by
  have h1 : some [encodeValue .int a] =
      (UnOp.evalT .toUint (p := .int) rfl a).map (fun b => [encodeValue .uint b]) :=
    toUint.correct a []
  change some [encodeValue .int a] =
    (UnOp.evalT .toUint (p := .int) rfl a).map (fun b => [encodeValue .uint b]) at h1
  cases hx : UnOp.evalT .toUint (p := .int) rfl a with
  | none => simp only [hx, Option.map_none, reduceCtorEq] at h1
  | some b =>
    simp only [hx, Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at h1
    have h2 : some [encodeValue .uint b] =
        (UnOp.evalT .toInt (p := .uint) rfl b).map (fun c => [encodeValue .int c]) :=
      toInt.correct b []
    change some [encodeValue .uint b] =
      (UnOp.evalT .toInt (p := .uint) rfl b).map (fun c => [encodeValue .int c]) at h2
    cases hy : UnOp.evalT .toInt (p := .uint) rfl b with
    | none => simp only [hy, Option.map_none, reduceCtorEq] at h2
    | some c =>
      simp only [hy, Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at h2
      have hc : c = a := encode_int_injective (h2.symm.trans h1.symm)
      simp only [hy, Option.bind_some, hc]

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


#print axioms cast_roundtrip_uint
#print axioms cast_roundtrip_int

end Solidity.Backend.Scalar
