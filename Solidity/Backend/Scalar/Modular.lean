import Solidity.Backend.Scalar.Guards

/-! Source-exact modular builtin selection with wide intermediates and an
explicit zero-modulus failure-test boundary. The body and test are real
Backend programs. Generic branch/payload bytecode emission remains separate. -/
namespace Solidity.Backend.Scalar

def modularOutcome (op : ModOp) (a b k : PrimTy.uint.Denote) (tail : Stack) :
    Except (List UInt8) Stack :=
  match op.evalT a b k with
  | none => .error divisionFailure
  | some v => .ok (encodeValue .uint v :: tail)

def modularBody : ModOp → Program
  | .addmod => [.op .ADDMOD]
  | .mulmod => [.op .MULMOD]

theorem uint_word_zero (k : PrimTy.uint.Denote) :
    (encodeValue .uint k == 0) = decide (k.val = 0) := by
  have hk := uint_range k
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have hh := congrArg BitVec.toNat h
    rw [encode_uint_toNat] at hh
    change k.val.toNat = 0 at hh
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [encode_uint_toNat, h]
    rfl

/-- `addmod` agrees with the intrinsic builtin on both success and failure. -/
theorem addmod_correct (a b k : PrimTy.uint.Denote) (tail : Stack) :
    guarded (zeroTest ⟨2, by decide⟩) (modularBody .addmod) divisionFailure
      (encodeValue .uint a :: encodeValue .uint b :: encodeValue .uint k :: tail) =
      some (modularOutcome .addmod a b k tail) := by
  rw [guarded_zero ⟨2, by decide⟩ _ (encodeValue .uint k) _ _ rfl, uint_word_zero]
  by_cases hk : k.val = 0
  · simp only [hk, decide_true, if_true, modularOutcome, ModOp.evalT]
  · simp only [hk, decide_false]
    have hrk := uint_range k
    have hp : 0 < k.val := by omega
    have hn : PrimTy.uint.inRange (ModOp.wide .addmod a.val b.val % k.val) = true := by
      apply decide_eq_true
      exact ⟨Int.emod_nonneg _ (by omega),
        Int.lt_trans (Int.emod_lt_of_pos _ hp) hrk.2⟩
    have ha : a.val = (a.val.toNat : Int) := by have := uint_range a; omega
    have hb : b.val = (b.val.toNat : Int) := by have := uint_range b; omega
    have hkk : k.val = (k.val.toNat : Int) := by omega
    have he : BitVec.ofInt 256 (ModOp.wide .addmod a.val b.val % k.val) =
        BitVec.ofNat 256 ((a.val.toNat + b.val.toNat) % k.val.toNat) := by
      rw [ModOp.wide, ha, hb, hkk, ← Int.natCast_add, ← Int.natCast_emod,
        BitVec.ofInt_natCast]
      simp only [Int.toNat_natCast]
    simp only [modularBody, run, step, numericStep, unary, binary, ternary,
      applyTernary, uint_word_zero, hk, decide_false, Bool.false_eq_true, if_false, Option.bind_some,
      Option.map_some]
    rw [encode_uint_toNat, encode_uint_toNat, encode_uint_toNat]
    simp only [modularOutcome, ModOp.evalT, hk, if_false, PrimTy.ofInt?, hn,
      dite_true, encodeValue]
    rw [he]

/-- `mulmod` agrees with the intrinsic builtin on both success and failure. -/
theorem mulmod_correct (a b k : PrimTy.uint.Denote) (tail : Stack) :
    guarded (zeroTest ⟨2, by decide⟩) (modularBody .mulmod) divisionFailure
      (encodeValue .uint a :: encodeValue .uint b :: encodeValue .uint k :: tail) =
      some (modularOutcome .mulmod a b k tail) := by
  rw [guarded_zero ⟨2, by decide⟩ _ (encodeValue .uint k) _ _ rfl, uint_word_zero]
  by_cases hk : k.val = 0
  · simp only [hk, decide_true, if_true, modularOutcome, ModOp.evalT]
  · simp only [hk, decide_false]
    have hrk := uint_range k
    have hp : 0 < k.val := by omega
    have hn : PrimTy.uint.inRange (ModOp.wide .mulmod a.val b.val % k.val) = true := by
      apply decide_eq_true
      exact ⟨Int.emod_nonneg _ (by omega),
        Int.lt_trans (Int.emod_lt_of_pos _ hp) hrk.2⟩
    have ha : a.val = (a.val.toNat : Int) := by have := uint_range a; omega
    have hb : b.val = (b.val.toNat : Int) := by have := uint_range b; omega
    have hkk : k.val = (k.val.toNat : Int) := by omega
    have he : BitVec.ofInt 256 (ModOp.wide .mulmod a.val b.val % k.val) =
        BitVec.ofNat 256 ((a.val.toNat * b.val.toNat) % k.val.toNat) := by
      rw [ModOp.wide, ha, hb, hkk, ← Int.natCast_mul, ← Int.natCast_emod,
        BitVec.ofInt_natCast]
      simp only [Int.toNat_natCast]
    simp only [modularBody, run, step, numericStep, unary, binary, ternary,
      applyTernary, uint_word_zero, hk, decide_false, Bool.false_eq_true, if_false, Option.bind_some,
      Option.map_some]
    rw [encode_uint_toNat, encode_uint_toNat, encode_uint_toNat]
    simp only [modularOutcome, ModOp.evalT, hk, if_false, PrimTy.ofInt?, hn,
      dite_true, encodeValue]
    rw [he]

/-- Word overflow must not occur before the modular reduction. -/
example : run (modularBody .addmod) [BitVec.ofInt 256 (-1), 1, 7, 99] =
    some [2, 99] := by decide +kernel
example : run (modularBody .mulmod) [BitVec.ofInt 256 (-1), 2, 7, 99] =
    some [2, 99] := by decide +kernel
example : guarded (zeroTest ⟨2, by decide⟩) (modularBody .addmod) divisionFailure [7, 2, 0, 99] =
    some (.error divisionFailure) := rfl

/-- info: 'Solidity.Backend.Scalar.addmod_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms addmod_correct
/-- info: 'Solidity.Backend.Scalar.mulmod_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mulmod_correct

end Solidity.Backend.Scalar
