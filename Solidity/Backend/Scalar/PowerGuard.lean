import Solidity.Backend.Scalar.PowerBounds
import Solidity.Backend.Scalar.UnsignedMul
import Solidity.Backend.Scalar.Exponentiation

/-! Finite checked-power selection. Kernel-verified thresholds cover exponents
1 through 255; bases 0/1 and exponent zero are handled independently, and
larger exponents at base at least two cannot fit any existing scalar width. -/
namespace Solidity.Backend.Scalar

theorem threshold_accept (w : Fin 32) (i : Fin 255) (a : Nat) :
    a ≤ naturalThresholds[w][i] ↔ a ^ (i.val+1) < 2 ^ widthBits w := by
  obtain ⟨_, hlo, hhi⟩ := threshold_bounds w i
  constructor
  · intro ha
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_left ha _) hlo
  · intro ha
    by_cases hn : a ≤ naturalThresholds[w][i]
    · exact hn
    exfalso
    have hle : naturalThresholds[w][i]+1 ≤ a := by omega
    have hp : (naturalThresholds[w][i] + 1) ^ (i.val + 1) ≤ a ^ (i.val + 1) := Nat.pow_le_pow_left hle (i.val+1)
    omega

def powerFits (w : Fin 32) (a n : Nat) : Bool :=
  decide (a ≤ 1) || decide (n = 0) ||
    (List.finRange 255).any (fun i => decide (n = i.val+1) && decide (a ≤ naturalThresholds[w][i]))

theorem powerFits_correct (w : Fin 32) (a n : Nat) :
    powerFits w a n = decide (a^n < 2 ^ widthBits w) := by
  have hb : 1 < 2 ^ widthBits w := Nat.one_lt_two_pow (by have : 8 ≤ widthBits w ∧ widthBits w ≤ 256 := widthBits_bounds w; omega)
  apply Bool.eq_iff_iff.mpr
  simp only [powerFits, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.and_eq_true]
  constructor
  · intro h
    rcases h with (ha | hn) | ⟨i, _, hn, ha⟩
    · have hp : a^n ≤ 1 := by simpa only [Nat.one_pow] using Nat.pow_le_pow_left ha n
      omega
    · rw [hn, Nat.pow_zero]; exact hb
    · rw [hn]; exact (threshold_accept w i a).mp ha
  · intro h
    by_cases ha : a ≤ 1
    · exact Or.inl (Or.inl ha)
    by_cases hn : n = 0
    · exact Or.inl (Or.inr hn)
    have hsmall : n < 256 := by
      by_cases hlarge : n < 256
      · exact hlarge
      exfalso
      have hp : 2 ^ n ≤ a ^ n := Nat.pow_le_pow_left (show 2 ≤ a by omega) n
      have he : 2 ^ 256 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) (show 256 ≤ n by omega)
      have hw : 2 ^ widthBits w ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide : 0 < 2) (widthBits_bounds w).2
      omega
    let i : Fin 255 := ⟨n-1, by omega⟩
    have hi : n = i.val+1 := by dsimp only [i]; omega
    refine Or.inr ⟨i, ?_, hi, ?_⟩
    · simp only [List.finRange, List.mem_ofFn]
      exact ⟨i, rfl⟩
    · apply (threshold_accept w i a).mpr
      rw [← hi]
      exact h


theorem flag_and (a b : Bool) : flag a &&& flag b = flag (a && b) := by
  cases a <;> cases b <;> rfl

def powerCell (w : Fin 32) (i : Fin 255) : Program :=
  [.op (.DUP ⟨2, by decide⟩), pushWord (exponentWord i), .op .EQ,
   .op (.DUP ⟨2, by decide⟩), pushWord (thresholdWord w i), .op .LT,
   .op .ISZERO, .op .AND, .op .OR]

def cellAccept (w : Fin 32) (i : Fin 255) (a n : Word) : Bool :=
  decide (n.toNat = i.val+1) && decide (a.toNat ≤ naturalThresholds[w][i])


private theorem stepDup3 (a b c : Word) (tail : Stack) :
    step (.op (.DUP ⟨2, by decide⟩)) (a::b::c::tail) = some (c::a::b::c::tail) := rfl
private theorem stepEq (a b : Word) (tail : Stack) :
    step (.op .EQ) (a::b::tail) = some (flag (a==b)::tail) := rfl
private theorem stepLt (a b : Word) (tail : Stack) :
    step (.op .LT) (a::b::tail) = some (flag (decide (a.toNat<b.toNat))::tail) := rfl
private theorem stepZero (a : Word) (tail : Stack) :
    step (.op .ISZERO) (a::tail) = some (flag (a==0)::tail) := rfl
private theorem stepAnd (a b : Word) (tail : Stack) :
    step (.op .AND) (a::b::tail) = some ((a &&& b)::tail) := rfl
private theorem stepOr (a b : Word) (tail : Stack) :
    step (.op .OR) (a::b::tail) = some ((a ||| b)::tail) := rfl

theorem powerCell_correct (w : Fin 32) (i : Fin 255)
    (acc : Bool) (a n : Word) (tail : Stack) :
    run (powerCell w i) (flag acc :: a :: n :: tail) =
      some (flag (cellAccept w i a n || acc) :: a :: n :: tail) := by
  simp only [powerCell, run, stepDup3, step_pushWord, stepEq, stepLt,
    stepZero, stepAnd, stepOr, Option.bind_some]
  rw [flag_iszero, flag_and, flag_or, thresholdWord_nat]
  have he : (exponentWord i == n) = decide (n.toNat = i.val+1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, BitVec.toNat_eq, exponentWord_nat]
    omega
  have hn : (!decide (naturalThresholds[w][i] < a.toNat)) =
      decide (a.toNat ≤ naturalThresholds[w][i]) := by
    simp only [← decide_not, Nat.not_lt]
  rw [he, hn, Bool.and_comm]
  rfl

def powerRows (w : Fin 32) (is : List (Fin 255)) : Program := is.flatMap (powerCell w)

theorem powerRows_correct (w : Fin 32) (is : List (Fin 255))
    (acc : Bool) (a n : Word) (tail : Stack) :
    run (powerRows w is) (flag acc :: a :: n :: tail) =
      some (flag (is.any (fun i => cellAccept w i a n) || acc) :: a :: n :: tail) := by
  induction is generalizing acc with
  | nil => rfl
  | cons i is ih =>
    change run (powerCell w i ++ powerRows w is) _ = _
    rw [run_append, powerCell_correct, Option.bind_some, ih]
    simp only [List.any_cons]
    rw [← Bool.or_assoc, Bool.or_comm (is.any _), Bool.or_assoc]

def powerStart : Program :=
  [.op (.DUP ⟨1, by decide⟩), .op .ISZERO, .op (.DUP ⟨1, by decide⟩),
   pushWord 1, .op .LT, .op .ISZERO, .op .OR]

theorem powerStart_correct (a n : Word) (tail : Stack) :
    run powerStart (a :: n :: tail) =
      some (flag (decide (a.toNat ≤ 1) || decide (n.toNat = 0)) :: a :: n :: tail) := by
  change run (pushWord 1 :: _) (a :: flag (n == 0) :: a :: n :: tail) = _
  rw [run, step_pushWord]
  change some ((flag (flag (decide (1 < a.toNat)) == 0) ||| flag (n == 0)) :: a :: n :: tail) = _
  rw [flag_iszero, flag_or]
  have he : (n == 0) = decide (n.toNat = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, BitVec.toNat_eq]
    rfl
  have hn : (!decide (1 < a.toNat)) = decide (a.toNat ≤ 1) := by
    simp only [← decide_not, Nat.not_lt]
  rw [he, hn]

def powerTest (w : Fin 32) : Program :=
  powerStart ++ powerRows w (List.finRange 255) ++ [.op .ISZERO]

theorem powerTest_correct (w : Fin 32) (a n : Word) (tail : Stack) :
    run (powerTest w) (a :: n :: tail) =
      some (flag (!decide (a.toNat ^ n.toNat < 2 ^ widthBits w)) :: a :: n :: tail) := by
  rw [powerTest, run_append, run_append, powerStart_correct, Option.bind_some,
    powerRows_correct, Option.bind_some]
  change some (flag (flag ((List.finRange 255).any (fun i => cellAccept w i a n) ||
    (decide (a.toNat ≤ 1) || decide (n.toNat = 0))) == 0) :: a :: n :: tail) = _
  rw [flag_iszero, Bool.or_comm]
  change some (flag (!powerFits w a.toNat n.toNat) :: a :: n :: tail) = _
  rw [powerFits_correct]


def checkedUintPow : CheckedCertificate .pow .uint rfl where
  test := powerTest ⟨31, by decide⟩
  body := [.op .EXP]
  correct := by
    intro a b tail
    have hb : ¬ b.val < 0 := by have : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b; omega
    change guarded _ _ _ _ = some (checkedOutcome .uint
      ((if b.val < 0 then none else some (a.val ^ b.val.toNat)).bind PrimTy.uint.ofInt?) tail)
    simp only [hb, if_false, Option.bind_some]
    apply guarded_range_correct _ _ a b (a.val ^ b.val.toNat) tail
    · rw [powerTest_correct, encode_uint_toNat, encode_uint_toNat]
      have ha : a.val = (a.val.toNat : Int) := by have : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a; omega
      have hp : a.val ^ b.val.toNat = ((a.val.toNat ^ b.val.toNat : Nat) : Int) := by
        rw [ha, ← Int.natCast_pow]
        simp only [Int.toNat_natCast]
      have he : PrimTy.uint.inRange (a.val ^ b.val.toNat) =
          decide (a.val.toNat ^ b.val.toNat < 2 ^ 256) := by
        apply Bool.eq_iff_iff.mpr
        simp only [PrimTy.inRange, decide_eq_true_eq, hp]
        omega
      rw [he]
      rfl
    · change some (BitVec.ofNat 256
        ((encodeValue .uint a).toNat ^ (encodeValue .uint b).toNat) :: tail) = _
      rw [encode_uint_toNat, encode_uint_toNat]
      have ha : a.val = (a.val.toNat : Int) := by have : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a; omega
      rw [ha, ← Int.natCast_pow, BitVec.ofInt_natCast]
      simp only [Int.toNat_natCast]

#print axioms checkedUintPow

#print axioms powerCell_correct
#print axioms powerRows_correct
#print axioms powerTest_correct

#print axioms threshold_accept
#print axioms powerFits_correct
end Solidity.Backend.Scalar
