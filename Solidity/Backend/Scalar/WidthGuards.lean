import Solidity.Backend.Scalar.SignedGuards
import Solidity.Backend.Scalar.FixedBytes

/-! Runtime width checks for the existing checked-narrow arithmetic boundary.
Explicit numeric conversions remain truncating/reinterpreting as defined by
the source; these checks are not inserted into such casts. The enclosing
source overflow/require mode owns the choice of supplied failure data. -/
namespace Solidity.Backend.Scalar

def unsignedMaximum (w : Fin 32) : PrimTy.uint.Denote :=
  ⟨((2^widthBits w-1:Nat):Int), by
    have hb := Nat.pow_le_pow_right (by decide : 0<2) (widthBits_bounds w).2
    have hp := Nat.pow_pos (by decide : 0<2) (n := widthBits w)
    simp only [PrimTy.inRange, decide_eq_true_eq]
    constructor
    · exact Int.natCast_nonneg _
    · omega⟩

def signedMinimum (w : Fin 32) : PrimTy.int.Denote :=
  ⟨-((2^(widthBits w-1):Nat):Int), by
    have hb := Nat.pow_le_pow_right (by decide : 0<2)
      (show widthBits w-1≤255 by have := widthBits_bounds w; omega)
    have hp := Nat.pow_pos (by decide : 0<2) (n := widthBits w-1)
    simp only [PrimTy.inRange, decide_eq_true_eq]
    omega⟩

def signedMaximum (w : Fin 32) : PrimTy.int.Denote :=
  ⟨((2^(widthBits w-1)-1:Nat):Int), by
    have hb := Nat.pow_le_pow_right (by decide : 0<2)
      (show widthBits w-1≤255 by have := widthBits_bounds w; omega)
    have hp := Nat.pow_pos (by decide : 0<2) (n := widthBits w-1)
    simp only [PrimTy.inRange, decide_eq_true_eq]
    omega⟩

def unsignedWidthTest (w : Fin 32) : Program :=
  [.op (.DUP ⟨0, by decide⟩), pushWord (encodeValue .uint (unsignedMaximum w)), .op .LT]

def signedWidthTest (w : Fin 32) : Program :=
  [.op (.DUP ⟨0, by decide⟩), pushWord (encodeValue .int (signedMinimum w)),
   .op (.SWAP ⟨0, by decide⟩), .op .SLT,
   .op (.DUP ⟨1, by decide⟩), pushWord (encodeValue .int (signedMaximum w)), .op .SLT, .op .OR]

def unsignedFits (w : Fin 32) (a : PrimTy.uint.Denote) : Bool :=
  decide (a.val < ((2^widthBits w:Nat):Int))

def signedFits (w : Fin 32) (a : PrimTy.int.Denote) : Bool :=
  decide (-((2^(widthBits w-1):Nat):Int) ≤ a.val ∧ a.val < ((2^(widthBits w-1):Nat):Int))


private theorem stepDup1 (a : Word) (tail : Stack) :
    step (.op (.DUP ⟨0, by decide⟩)) (a::tail) = some (a::a::tail) := rfl
private theorem stepDup2 (a b : Word) (tail : Stack) :
    step (.op (.DUP ⟨1, by decide⟩)) (a::b::tail) = some (b::a::b::tail) := rfl
private theorem stepSwap1 (a b : Word) (tail : Stack) :
    step (.op (.SWAP ⟨0, by decide⟩)) (a::b::tail) = some (b::a::tail) := rfl
private theorem stepLT (a b : Word) (tail : Stack) :
    step (.op .LT) (a::b::tail) = some (flag (decide (a.toNat<b.toNat))::tail) := rfl
private theorem stepSLT (a b : Word) (tail : Stack) :
    step (.op .SLT) (a::b::tail) = some (flag (decide (a.toInt<b.toInt))::tail) := rfl
private theorem stepOR (a b : Word) (tail : Stack) :
    step (.op .OR) (a::b::tail) = some ((a ||| b)::tail) := rfl

theorem unsignedWidthTest_correct (w : Fin 32) (a : PrimTy.uint.Denote) (tail : Stack) :
    run (unsignedWidthTest w) (encodeValue .uint a::tail) =
      some (flag (!unsignedFits w a)::encodeValue .uint a::tail) := by
  simp only [unsignedWidthTest, run, stepDup1, step_pushWord, stepLT, Option.bind_some]
  rw [encode_uint_toNat, encode_uint_toNat]
  have ha := uint_range a
  have hp := Nat.pow_pos (by decide : 0<2) (n := widthBits w)
  have he : decide ((unsignedMaximum w).val.toNat < a.val.toNat) = !unsignedFits w a := by
    apply Bool.eq_iff_iff.mpr
    simp only [unsignedMaximum, Int.toNat_natCast, unsignedFits, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  rw [he]

theorem signedWidthTest_correct (w : Fin 32) (a : PrimTy.int.Denote) (tail : Stack) :
    run (signedWidthTest w) (encodeValue .int a::tail) =
      some (flag (!signedFits w a)::encodeValue .int a::tail) := by
  simp only [signedWidthTest, run, stepDup1, step_pushWord, stepSwap1,
    stepDup2, stepSLT, stepOR, Option.bind_some]
  rw [flag_or]
  simp only [encode_int_toInt]
  have hp := Nat.pow_pos (by decide : 0<2) (n := widthBits w-1)
  have he : (decide ((signedMaximum w).val < a.val) || decide (a.val < (signedMinimum w).val)) =
      !signedFits w a := by
    apply Bool.eq_iff_iff.mpr
    simp only [signedMaximum, signedMinimum, signedFits, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  rw [he]


theorem unsignedWidth_guarded (w : Fin 32) (a : PrimTy.uint.Denote) (tail : Stack)
    (failure : List UInt8) :
    guarded (unsignedWidthTest w) [] failure (encodeValue .uint a::tail) =
      some (if unsignedFits w a then .ok (encodeValue .uint a::tail) else .error failure) := by
  unfold guarded
  rw [unsignedWidthTest_correct]
  cases hf : unsignedFits w a <;> rfl

theorem signedWidth_guarded (w : Fin 32) (a : PrimTy.int.Denote) (tail : Stack)
    (failure : List UInt8) :
    guarded (signedWidthTest w) [] failure (encodeValue .int a::tail) =
      some (if signedFits w a then .ok (encodeValue .int a::tail) else .error failure) := by
  unfold guarded
  rw [signedWidthTest_correct]
  cases hf : signedFits w a <;> rfl

example : guarded (unsignedWidthTest ⟨0, by decide⟩) [] overflowFailure [256,99] =
    some (.error overflowFailure) := rfl
example : guarded (signedWidthTest ⟨0, by decide⟩) [] overflowFailure [127,99] =
    some (.ok [127,99]) := rfl
example : guarded (signedWidthTest ⟨0, by decide⟩) [] overflowFailure
    [BitVec.ofInt 256 (-129),99] = some (.error overflowFailure) := rfl

#print axioms unsignedWidth_guarded
#print axioms signedWidth_guarded

#print axioms unsignedWidthTest_correct
#print axioms signedWidthTest_correct
end Solidity.Backend.Scalar
