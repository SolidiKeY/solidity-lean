import Solidity.Backend.Scalar.Division
import Solidity.Backend.Scalar.SignedBits
import Solidity.Evm.Signed

/-! Signed division bodies reuse the committed independent range theorems.
The exceptional minimum divided by -1 case and zero divisors are excluded only from the
successful body theorem; their exceptional source behavior is proved below. -/
namespace Solidity.Backend.Scalar

theorem int_word_zero (a : PrimTy.int.Denote) :
    (encodeValue .int a == 0) = decide (a.val = 0) := by
  have he : encodeValue .int a = 0 ↔ a.val = 0 := by
    constructor
    · intro h
      have hh : BitVec.toInt (encodeValue PrimTy.int a) = BitVec.toInt 0 := congrArg BitVec.toInt h
      rw [encode_int_toInt] at hh
      exact hh
    · intro h
      change BitVec.ofInt 256 a.val = 0
      rw [h]
      rfl
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, he]

theorem int_div_body (a b : PrimTy.int.Denote) (hb : b.val ≠ 0)
    (hn : ¬ (a.val = -((2^255 : Nat) : Int) ∧ b.val = -1)) (tail : Stack) :
    run [.op .SDIV] (encodeValue .int a :: encodeValue .int b :: tail) =
      (BinOp.evalT .div (p := .int) rfl a b).map
        (fun v => encodeValue .int v :: tail) := by
  have hr : PrimTy.int.inRange (a.val.tdiv b.val) = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact (Evm.tdiv_range (int_range a) hb).mpr hn
  have hz : (encodeValue .int b == 0) = false := by
    rw [int_word_zero]
    exact decide_eq_false hb
  change some ((if encodeValue .int b == 0 then 0 else
    BitVec.ofInt 256 ((encodeValue .int a).toInt.tdiv (encodeValue .int b).toInt)) :: tail) =
    ((if b.val = 0 then none else some (a.val.tdiv b.val)).bind PrimTy.int.ofInt?).map
      (fun v => encodeValue .int v :: tail)
  simp only [hz, Bool.false_eq_true, if_false, hb, Option.bind_some,
    encode_int_toInt]
  exact (encoded_int _ hr tail).symm

theorem int_mod_body (a b : PrimTy.int.Denote) (hb : b.val ≠ 0) (tail : Stack) :
    run [.op .SMOD] (encodeValue .int a :: encodeValue .int b :: tail) =
      (BinOp.evalT .mod (p := .int) rfl a b).map
        (fun v => encodeValue .int v :: tail) := by
  have hr : PrimTy.int.inRange (a.val.tmod b.val) = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact Evm.tmod_range (int_range b) hb
  have hz : (encodeValue .int b == 0) = false := by
    rw [int_word_zero]
    exact decide_eq_false hb
  change some ((if encodeValue .int b == 0 then 0 else
    BitVec.ofInt 256 ((encodeValue .int a).toInt.tmod (encodeValue .int b).toInt)) :: tail) =
    ((if b.val = 0 then none else some (a.val.tmod b.val)).bind PrimTy.int.ofInt?).map
      (fun v => encodeValue .int v :: tail)
  simp only [hz, Bool.false_eq_true, if_false, hb, Option.bind_some,
    encode_int_toInt]
  exact (encoded_int _ hr tail).symm

/-- The source cannot return the raw EVM signed-division overflow word. -/
theorem int_div_exception (a b : PrimTy.int.Denote)
    (ha : a.val = -((2^255 : Nat) : Int)) (hb : b.val = -1) :
    BinOp.evalT .div (p := .int) rfl a b = none := by
  change ((if b.val = 0 then none else some (a.val.tdiv b.val)).bind PrimTy.int.ofInt?) = none
  rw [ha, hb]
  decide +kernel

example : run [.op .SDIV] [BitVec.ofInt 256 (-7), 2, 99] =
    some [BitVec.ofInt 256 (-3), 99] := by decide +kernel
example : run [.op .SMOD] [BitVec.ofInt 256 (-7), 2, 99] =
    some [BitVec.ofInt 256 (-1), 99] := by decide +kernel
example : run [.op .SDIV] [BitVec.ofInt 256 (-((2^255:Nat):Int)),
    BitVec.ofInt 256 (-1), 99] =
    some [BitVec.ofInt 256 (-((2^255:Nat):Int)), 99] := by decide +kernel

#print axioms int_word_zero
#print axioms int_div_body
#print axioms int_mod_body
#print axioms int_div_exception
end Solidity.Backend.Scalar
