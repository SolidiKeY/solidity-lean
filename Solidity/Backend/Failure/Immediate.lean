import Solidity.Backend.Opcode

/-!
# Machine immediates for the failure slice

This encodes machine integers, not ABI values. The ABI payload stays opaque.
All immediates use PUSH32; the proof exposes the exact big-endian reading.
-/
namespace Solidity.Backend.Failure

def wordLimit : Nat := 256 ^ 32

def digits : (width : Nat) → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => digits k (n / 256) ++ [UInt8.ofNat (n % 256)]

theorem digits_length (k n : Nat) : (digits k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [digits, List.length_append, ih, List.length_cons,
      List.length_nil]

def readImmediate (bs : List UInt8) : Nat :=
  bs.foldl (fun a b => a * 256 + b.toNat) 0

theorem digits_fold (k n a : Nat) (h : n < 256 ^ k) :
    (digits k n).foldl (fun a b => a * 256 + b.toNat) a = a * 256 ^ k + n := by
  induction k generalizing n a with
  | zero =>
    have hn : n = 0 := by simpa only [Nat.pow_zero] using Nat.eq_zero_of_le_zero (by omega : n ≤ 0)
    subst n
    simp only [digits, List.foldl_nil, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
  | succ k ih =>
    have hd : n / 256 < 256 ^ k := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2
      simpa only [Nat.pow_succ] using h
    rw [digits, List.foldl_append, ih _ _ hd]
    simp only [List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat',
      Nat.mod_mod, Nat.add_mul, Nat.mul_assoc, Nat.pow_succ]
    have hn : n / 256 * 256 + n % 256 = n := by omega
    omega

theorem read_digits (k n : Nat) (h : n < 256 ^ k) :
    readImmediate (digits k n) = n := by
  simpa only [readImmediate, Nat.zero_mul, Nat.zero_add] using digits_fold k n 0 h

def pushNat (n : Nat) : Instr :=
  .push ⟨32, by decide⟩ ⟨(digits 32 n).toArray, by simp only [List.size_toArray, digits_length]⟩

theorem pushNat_immediate (n : Nat) :
    (match pushNat n with | .push _ v => v.toList | .op _ => []) = digits 32 n := by
  simp only [pushNat, Vector.toList]

theorem encode_pushNat (n : Nat) : (pushNat n).encode = 0x7f :: digits 32 n := by
  simp only [pushNat, Instr.encode, Vector.toList, pushCode]
  rfl

end Solidity.Backend.Failure
