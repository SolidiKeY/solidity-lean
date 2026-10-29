import Solidity.Backend.Scalar.Slice

/-!
# Width cleanup at existing byte-multiple scalar widths

`Fin 32` records the byte count minus one, covering 8 through 256 bits.
This is metadata for the existing intrinsic primitive types, not a new
source value or term language. Source width expansion and fixed-bytes markers
remain owned by the existing elaborator. These cleanup laws are the local
instruction contracts needed to relate that expansion to numeric stack code.
-/
namespace Solidity.Backend.Scalar

/-- Every Solidity integer/fixed-bytes width is a nonempty number of bytes. -/
def widthBits (w : Fin 32) : Nat := 8 * (w.val + 1)

theorem widthBits_bounds (w : Fin 32) : 8 ≤ widthBits w ∧ widthBits w ≤ 256 := by
  unfold widthBits
  omega

/-- Independent unsigned truncation to the declared low bits. -/
def unsignedClean (w : Fin 32) (x : Word) : Word :=
  BitVec.ofNat 256 (x.toNat % 2 ^ widthBits w)

/-- Independent signed truncation and two's-complement extension. -/
def signedClean (w : Fin 32) (x : Word) : Word :=
  let low := x.toNat % 2 ^ widthBits w
  BitVec.ofInt 256 (if low < 2 ^ (widthBits w - 1) then (low : Int)
    else (low : Int) - (2 ^ widthBits w : Nat))

/-- Unsigned normalization is a mask with an actual concrete immediate. -/
def unsignedCode (w : Fin 32) : Program :=
  [pushWord (BitVec.ofNat 256 (2 ^ widthBits w - 1)), .op .AND]

/-- Signed normalization uses SIGNEXTEND's byte index, not its bit count. -/
def signedCode (w : Fin 32) : Program :=
  [pushWord (BitVec.ofNat 256 w.val), .op .SIGNEXTEND]

theorem unsigned_correct (w : Fin 32) (x : Word) (tail : Stack) :
    run (unsignedCode w) (x :: tail) = some (unsignedClean w x :: tail) := by
  have hp : 2 ^ widthBits w ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (widthBits_bounds w).2
  have hm : 2 ^ widthBits w - 1 < 2 ^ 256 := by
    have hpos : 0 < 2 ^ widthBits w := Nat.pow_pos (by decide)
    omega
  rw [unsignedCode, run, step_pushWord]
  change some ((BitVec.ofNat 256 (2 ^ widthBits w - 1) &&& x) :: tail) = _
  have he : BitVec.ofNat 256 (2 ^ widthBits w - 1) &&& x = unsignedClean w x := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm,
      unsignedClean, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by decide))) hp)]
  rw [he]

theorem signed_correct (w : Fin 32) (x : Word) (tail : Stack) :
    run (signedCode w) (x :: tail) = some (signedClean w x :: tail) := by
  have hw : w.val < 2 ^ 256 := by have := w.isLt; omega
  rw [signedCode, run, step_pushWord]
  simp only [run, step, duplicateIndex, unary, binary, applyBinary, Option.bind_some, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hw, w.isLt, if_true, signedClean, widthBits]

/-- Truncating first to a wider unsigned width and then a narrower one
is the same as truncating directly to the narrower width. -/
theorem unsigned_chain (a b : Fin 32) (hab : widthBits a ≤ widthBits b) (x : Word) :
    unsignedClean a (unsignedClean b x) = unsignedClean a x := by
  have hp : 2 ^ widthBits b ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (widthBits_bounds b).2
  have hx : x.toNat % 2 ^ widthBits b < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by decide))) hp
  simp only [unsignedClean, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hab)]

/-- A concrete narrowing boundary, plus the old bare-ADD negative control. -/
example : unsignedClean ⟨0, by decide⟩ (256 : Word) = 0 := by decide +kernel
example : (256 : Word) ≠ unsignedClean ⟨0, by decide⟩ 256 := by decide +kernel
example : signedClean ⟨0, by decide⟩ (255 : Word) = BitVec.ofInt 256 (-1) := by decide +kernel

/-- SIGNEXTEND's index is measured in bytes. -/
example : run (signedCode ⟨1, by decide⟩) [128, 99] = some [128, 99] := by decide +kernel

/-- info: 'Solidity.Backend.Scalar.unsigned_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsigned_correct
/-- info: 'Solidity.Backend.Scalar.signed_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms signed_correct
/-- info: 'Solidity.Backend.Scalar.unsigned_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unsigned_chain

end Solidity.Backend.Scalar
