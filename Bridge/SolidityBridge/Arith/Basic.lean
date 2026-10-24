import Solidity.Semantics.Ops
import Init.Data.BitVec.Bitblast
import Mathlib.Data.ZMod.Basic

/-!
# Arithmetic against library words and modular integers

These statements read the actual typed evaluator, including its range check.
They cover checked add/subtract/multiply at both numeric types, and wrapping
unsigned arithmetic at 256 bits. Narrow Solidity types are lowered by the
elaborator; these are the primitive evaluator's types, not a theorem about
every elaborated source expression.
-/

set_option maxRecDepth 2048

namespace Solidity.Bridge.Arith

theorem uint_check (n : Int) :
    (PrimTy.uint.ofInt? n).map Subtype.val =
      if 0 ≤ n ∧ n < 2 ^ 256 then some n else none := by
  simp only [PrimTy.ofInt?, PrimTy.inRange, decide_eq_true_eq, Nat.cast_pow, Nat.cast_ofNat]
  split <;> simp_all only [Option.map_some, Option.map_none]

theorem int_check (n : Int) :
    (PrimTy.int.ofInt? n).map Subtype.val =
      if -(2 ^ 255) ≤ n ∧ n < 2 ^ 255 then some n else none := by
  simp only [PrimTy.ofInt?, PrimTy.inRange, decide_eq_true_eq, Nat.cast_pow, Nat.cast_ofNat]
  split <;> simp_all only [Option.map_some, Option.map_none]

theorem uint_add (x y : PrimTy.uint.Denote) :
    (BinOp.add.evalT rfl x y).map Subtype.val =
      if 0 ≤ x.val + y.val ∧ x.val + y.val < 2 ^ 256 then some (x.val + y.val) else none :=
  uint_check _

theorem uint_sub (x y : PrimTy.uint.Denote) :
    (BinOp.sub.evalT rfl x y).map Subtype.val =
      if 0 ≤ x.val - y.val ∧ x.val - y.val < 2 ^ 256 then some (x.val - y.val) else none :=
  uint_check _

theorem uint_mul (x y : PrimTy.uint.Denote) :
    (BinOp.mul.evalT rfl x y).map Subtype.val =
      if 0 ≤ x.val * y.val ∧ x.val * y.val < 2 ^ 256 then some (x.val * y.val) else none :=
  uint_check _

theorem int_add (x y : PrimTy.int.Denote) :
    (BinOp.add.evalT rfl x y).map Subtype.val =
      if -(2 ^ 255) ≤ x.val + y.val ∧ x.val + y.val < 2 ^ 255 then some (x.val + y.val) else none :=
  int_check _

theorem int_sub (x y : PrimTy.int.Denote) :
    (BinOp.sub.evalT rfl x y).map Subtype.val =
      if -(2 ^ 255) ≤ x.val - y.val ∧ x.val - y.val < 2 ^ 255 then some (x.val - y.val) else none :=
  int_check _

theorem int_mul (x y : PrimTy.int.Denote) :
    (BinOp.mul.evalT rfl x y).map Subtype.val =
      if -(2 ^ 255) ≤ x.val * y.val ∧ x.val * y.val < 2 ^ 255 then some (x.val * y.val) else none :=
  int_check _

theorem uint_mod (n : Int) :
    (PrimTy.uint.ofInt? (n % Semantics.uintBound)).map Subtype.val =
      some (n % Semantics.uintBound) := by
  have hb : 0 < Semantics.uintBound := Int.natCast_pos.mpr (Nat.two_pow_pos 256)
  rw [uint_check, if_pos]
  constructor
  · exact Int.emod_nonneg _ (ne_of_gt hb)
  · simpa only [Semantics.uintBound, Nat.cast_pow, Nat.cast_ofNat] using
      Int.emod_lt_of_pos n hb

theorem uint_mod_map {α : Type} (f : Int → α) (n : Int) :
    (PrimTy.uint.ofInt? (n % Semantics.uintBound)).map (fun z => f z.val) =
      some (f (n % Semantics.uintBound)) := by
  simpa only [Option.map_map, Function.comp_def, Option.map_some] using
    congrArg (Option.map f) (uint_mod n)

/-- The primitive wrapping addition returns exactly Lean's 256-bit addition. -/
theorem uint_addW_bitvec (x y : PrimTy.uint.Denote) :
    (BinOp.addW.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toNat : Int) := by
  rw [← BitVec.ofInt_add, BitVec.toNat_ofInt, Int.toNat_of_nonneg
    (Int.emod_nonneg _ (by omega))]
  exact uint_mod _

/-- The primitive wrapping multiplication returns Lean's 256-bit product. -/
theorem uint_mulW_bitvec (x y : PrimTy.uint.Denote) :
    (BinOp.mulW.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toNat : Int) := by
  rw [← BitVec.ofInt_mul, BitVec.toNat_ofInt, Int.toNat_of_nonneg
    (Int.emod_nonneg _ (by omega))]
  exact uint_mod _

/-- Wrapping addition agrees with Mathlib's modular ring. -/
theorem uint_addW_zmod (x y : PrimTy.uint.Denote) :
    (BinOp.addW.evalT rfl x y).map (fun z => (z.val : ZMod (2 ^ 256))) =
      some ((x.val : ZMod (2 ^ 256)) + (y.val : ZMod (2 ^ 256))) := by
  change (PrimTy.uint.ofInt? ((x.val + y.val) % Semantics.uintBound)).map _ = _
  exact (uint_mod_map (fun n : Int => (n : ZMod (2 ^ 256))) (x.val + y.val)).trans
    (by simp only [Semantics.uintBound, ZMod.intCast_mod, Int.cast_add])

/-- Wrapping multiplication agrees with Mathlib's modular ring. -/
theorem uint_mulW_zmod (x y : PrimTy.uint.Denote) :
    (BinOp.mulW.evalT rfl x y).map (fun z => (z.val : ZMod (2 ^ 256))) =
      some ((x.val : ZMod (2 ^ 256)) * (y.val : ZMod (2 ^ 256))) := by
  change (PrimTy.uint.ofInt? ((x.val * y.val) % Semantics.uintBound)).map _ = _
  exact (uint_mod_map (fun n : Int => (n : ZMod (2 ^ 256))) (x.val * y.val)).trans
    (by simp only [Semantics.uintBound, ZMod.intCast_mod, Int.cast_mul])

/-- Wrapping subtraction agrees with the modular ring, including underflow. -/
theorem uint_subW_zmod (x y : PrimTy.uint.Denote) :
    (BinOp.subW.evalT rfl x y).map (fun z => (z.val : ZMod (2 ^ 256))) =
      some ((x.val : ZMod (2 ^ 256)) - (y.val : ZMod (2 ^ 256))) := by
  change (PrimTy.uint.ofInt? ((x.val - y.val) % Semantics.uintBound)).map _ = _
  exact (uint_mod_map (fun n : Int => (n : ZMod (2 ^ 256))) (x.val - y.val)).trans
    (by simp only [Semantics.uintBound, ZMod.intCast_mod, Int.cast_sub])

end Solidity.Bridge.Arith

namespace Solidity.Bridge.Arith

/-- A library word used as an actual core unsigned operand. -/
def unsigned (x : BitVec 256) : PrimTy.uint.Denote :=
  ⟨x.toNat, by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr x.isLt⟩⟩

/-- A library word used as an actual core signed operand. -/
def signed (x : BitVec 256) : PrimTy.int.Denote :=
  ⟨x.toInt, by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩⟩

theorem uint_roundtrip (n : Int) :
    n = ((BitVec.ofInt 256 n).toNat : Int) ↔ 0 ≤ n ∧ n < 2 ^ 256 := by
  constructor
  · intro h
    rw [h]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (BitVec.ofInt 256 n).isLt⟩
  · rintro ⟨hn, hb⟩
    simp only [BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat,
      Int.emod_eq_of_lt hn hb, Int.toNat_of_nonneg hn]

theorem int_roundtrip (n : Int) :
    n = (BitVec.ofInt 256 n).toInt ↔ -(2 ^ 255) ≤ n ∧ n < 2 ^ 255 := by
  constructor
  · intro h
    rw [h]
    exact ⟨BitVec.le_toInt _, BitVec.toInt_lt⟩
  · rintro ⟨hn, hb⟩
    exact (BitVec.toInt_ofInt_eq_self (w := 256) (by decide) hn hb).symm

/-- Failure is exactly loss of the unbounded integer in the unsigned word. -/
theorem uint_check_bitvec (n : Int) :
    (PrimTy.uint.ofInt? n).map Subtype.val =
      if n = ((BitVec.ofInt 256 n).toNat : Int) then some n else none := by
  simp only [uint_check, uint_roundtrip]

/-- Failure is exactly loss of the unbounded integer in the signed word. -/
theorem int_check_bitvec (n : Int) :
    (PrimTy.int.ofInt? n).map Subtype.val =
      if n = (BitVec.ofInt 256 n).toInt then some n else none := by
  simp only [int_check, int_roundtrip]

theorem unsigned_encode (x : BitVec 256) : BitVec.ofInt 256 (unsigned x).val = x := by
  exact BitVec.ofNat_toNat 256 x

theorem signed_encode (x : BitVec 256) : BitVec.ofInt 256 (signed x).val = x := by
  exact BitVec.ofInt_toInt

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_check_bitvec
#print axioms Solidity.Bridge.Arith.int_check_bitvec
#print axioms Solidity.Bridge.Arith.unsigned_encode
#print axioms Solidity.Bridge.Arith.signed_encode
