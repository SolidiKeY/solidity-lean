import Solidity.Backend.Scalar.PowerGuard
import Solidity.Backend.Scalar.SignedShift
import Solidity.Semantics.NumericLowering

/-! Real opcode preparation for the committed checked signed-power helper:
retain the result sign and compute the unsigned magnitude, including int256 min. -/
namespace Solidity.Backend.Scalar

def magnitudeValue (a : PrimTy.int.Denote) : PrimTy.uint.Denote :=
  ⟨(a.val.natAbs:Int), by
    have ha : -((2 ^ 255 : Nat) : Int) ≤ a.val ∧ a.val < ((2 ^ 255 : Nat) : Int) := int_range a
    rw [← NumericLowering.abs_word a.val ha]
    split
    all_goals
      simp only [PrimTy.inRange, decide_eq_true_eq]
      exact ⟨Int.emod_nonneg _ (by decide : Semantics.uintBound ≠ 0),
        Int.emod_lt_of_pos _ (by decide : 0 < Semantics.uintBound)⟩⟩

def powerNegative (a : PrimTy.int.Denote) (n : PrimTy.uint.Denote) : Bool :=
  decide (a.val<0 ∧ n.val.toNat%2=1)

theorem parity_word (n : Word) : n &&& 1#256 = flag (decide (n.toNat%2=1)) := by
  apply BitVec.eq_of_toNat_eq
  change (n &&& 1#256).toNat = _
  rw [BitVec.toNat_and]
  change n.toNat &&& 1 = _
  rw [Nat.and_one_is_mod]
  have hm : BitVec.toNat n % 2 < 2 := Nat.mod_lt n.toNat (by decide : 0<2)
  by_cases hn : n.toNat%2=1
  · simp only [hn, decide_true, flag, if_true]; rfl
  · simp only [hn, decide_false, flag]
    change n.toNat%2=0
    omega

def powerNegativePrefix : Program :=
  [.op (.DUP ⟨0, by decide⟩), pushWord 0, .op .SGT,
   .op (.DUP ⟨2, by decide⟩), pushWord 1, .op .AND, .op .AND,
   .op (.SWAP ⟨1, by decide⟩), .op (.SWAP ⟨0, by decide⟩)]

theorem powerNegativePrefix_correct (a : PrimTy.int.Denote) (n : PrimTy.uint.Denote) (tail : Stack) :
    run powerNegativePrefix (encodeValue .int a::encodeValue .uint n::tail) =
      some (encodeValue .int a::encodeValue .uint n::flag (powerNegative a n)::tail) := by
  change run (pushWord 0 :: _) (encodeValue .int a::encodeValue .int a::encodeValue .uint n::tail) = _
  rw [run, step_pushWord]
  change run (pushWord 1 :: _) (encodeValue .uint n::flag (decide ((encodeValue .int a).toInt<0))::
    encodeValue .int a::encodeValue .uint n::tail) = _
  rw [run, step_pushWord]
  change some (encodeValue .int a::encodeValue .uint n::
    ((1#256 &&& encodeValue .uint n) &&& flag (decide ((encodeValue .int a).toInt<0)))::tail) = _
  rw [BitVec.and_comm 1#256, parity_word, flag_and, encode_int_toInt, encode_uint_toNat,
    Bool.and_comm, ← Bool.decide_and]
  rfl

def powerAbsPrefix : Program :=
  [.op (.DUP ⟨0, by decide⟩), pushWord 255, .op .SAR,
   .op (.DUP ⟨0, by decide⟩), .op (.DUP ⟨2, by decide⟩), .op .XOR,
   .op .SUB, .op (.SWAP ⟨0, by decide⟩), .op .POP]

theorem powerAbsPrefix_correct (a : PrimTy.int.Denote) (tail : Stack) :
    run powerAbsPrefix (encodeValue .int a::tail) = some (encodeValue .uint (magnitudeValue a)::tail) := by
  change run (pushWord 255 :: _) (encodeValue .int a::encodeValue .int a::tail) = _
  rw [run, step_pushWord]
  change some (((encodeValue .int a ^^^ BitVec.ofInt 256 ((encodeValue .int a).toInt/(2^255:Int))) -
    BitVec.ofInt 256 ((encodeValue .int a).toInt/(2^255:Int)))::tail) = _
  rw [encode_int_toInt]
  have har : -((2 ^ 255 : Nat) : Int) ≤ a.val ∧ a.val < ((2 ^ 255 : Nat) : Int) := int_range a
  have hB : (2^255:Int)=((2^255:Nat):Int) := (Int.natCast_pow 2 255).symm
  by_cases ha : a.val<0
  · have hq : a.val/(2^255:Int) = -1 :=
      Int.ediv_eq_neg_one_of_neg_of_le ha (by rw [hB]; omega)
    rw [hq]
    have he : (encodeValue .int a ^^^ BitVec.ofInt 256 (-1)) - BitVec.ofInt 256 (-1) =
        -encodeValue .int a := by
      change (encodeValue .int a ^^^ (-1#256)) - (-1#256) = _
      rw [BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes, ← BitVec.neg_one_eq_allOnes,
        BitVec.sub_neg, ← BitVec.neg_eq_not_add]
    rw [he]
    change some ((-(BitVec.ofInt 256 a.val))::tail) = some (BitVec.ofInt 256 (a.val.natAbs:Int)::tail)
    rw [Int.ofNat_natAbs_of_nonpos (Int.le_of_lt ha), BitVec.ofInt_neg]
  · have hq : a.val/(2^255:Int) = 0 :=
      Int.ediv_eq_zero_of_lt (Int.le_of_not_gt ha) (by rw [hB]; exact har.2)
    rw [hq]
    change some (((encodeValue .int a ^^^ 0#256) - 0#256)::tail) = _
    rw [BitVec.xor_zero, BitVec.sub_zero]
    change some (BitVec.ofInt 256 a.val::tail) = some (BitVec.ofInt 256 (a.val.natAbs:Int)::tail)
    rw [← Int.eq_natAbs_of_nonneg (Int.le_of_not_gt ha)]

def powerPrepare : Program := powerNegativePrefix ++ powerAbsPrefix

theorem powerPrepare_correct (a : PrimTy.int.Denote) (n : PrimTy.uint.Denote) (tail : Stack) :
    run powerPrepare (encodeValue .int a::encodeValue .uint n::tail) =
      some (encodeValue .uint (magnitudeValue a)::encodeValue .uint n::flag (powerNegative a n)::tail) :=
  run_comp (powerNegativePrefix_correct a n tail)
    (powerAbsPrefix_correct a (encodeValue .uint n::flag (powerNegative a n)::tail))

#print axioms parity_word
#print axioms powerNegativePrefix_correct
#print axioms powerAbsPrefix_correct
#print axioms powerPrepare_correct
end Solidity.Backend.Scalar
