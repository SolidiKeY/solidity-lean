import Solidity.Backend.Scalar.Guards

/-! Checked unsigned addition/subtraction tests preserve operands and select
the existing overflow panic bytes. The component's guarded execution boundary
is explicit; generic bytecode branch/payload emission is not claimed. -/
namespace Solidity.Backend.Scalar

/-- Observation adapter over the existing intrinsic result; no compilation
or target execution participates in the source operation. -/
def checkedOutcome (p : PrimTy) (res : Option p.Denote) (tail : Stack) :
    Except (List UInt8) Stack :=
  res.elim (.error overflowFailure) (fun v => .ok (encodeValue p v :: tail))

structure CheckedCertificate (op : BinOp) (p : PrimTy) (h : op.accepts p = true) where
  test : Program
  body : Program
  correct : ∀ (a b : p.Denote) (tail : Stack),
    guarded test body overflowFailure (encodeValue p a :: encodeValue p b :: tail) =
      some (checkedOutcome (op.ret p) (op.evalT h a b) tail)

/-- Compose independently established test and body contracts with the original
range-checking source constructor. No desired target result is postulated. -/
theorem guarded_range_correct (test body : Program) (a b : PrimTy.uint.Denote)
    (n : Int) (tail : Stack)
    (ht : run test (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (flag (!PrimTy.uint.inRange n) :: encodeValue .uint a :: encodeValue .uint b :: tail))
    (hb : run body (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (BitVec.ofInt 256 n :: tail)) :
    guarded test body overflowFailure (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (checkedOutcome .uint (PrimTy.uint.ofInt? n) tail) := by
  unfold guarded
  rw [ht]
  cases hr : PrimTy.uint.inRange n with
  | false =>
    rw [show PrimTy.uint.ofInt? n = none by
      simp only [PrimTy.ofInt?, hr, Bool.false_eq_true, dite_false]]
    rfl
  | true =>
    rw [show PrimTy.uint.ofInt? n = some ⟨n, hr⟩ by
      simp only [PrimTy.ofInt?, hr, dite_true]]
    change (run body (encodeValue .uint a :: encodeValue .uint b :: tail)).map Except.ok =
      some (Except.ok (BitVec.ofInt 256 n :: tail))
    rw [hb]
    rfl

/-- Overflow test: compare an original operand against the wrapped sum. -/
def unsignedAddTest : Program :=
  [.op (.DUP ⟨1, by decide⟩), .op (.DUP ⟨1, by decide⟩), .op .ADD,
   .op (.DUP ⟨1, by decide⟩), .op .GT]

/-- Underflow test retains the two original operands. -/
def unsignedSubTest : Program :=
  [.op (.DUP ⟨1, by decide⟩), .op (.DUP ⟨1, by decide⟩), .op .LT]

theorem unsignedAddTest_raw (a b : Word) (tail : Stack) :
    run unsignedAddTest (a :: b :: tail) =
      some (flag (decide (2 ^ 256 ≤ a.toNat + b.toNat)) :: a :: b :: tail) := by
  change some (flag (decide ((a + b).toNat < a.toNat)) :: a :: b :: tail) = _
  rw [BitVec.toNat_add]
  have ha : BitVec.toNat a < 2 ^ 256 := a.isLt
  have hb : BitVec.toNat b < 2 ^ 256 := b.isLt
  have he : ((a.toNat + b.toNat) % 2 ^ 256 < a.toNat) ↔
      2 ^ 256 ≤ a.toNat + b.toNat := by
    by_cases hs : a.toNat + b.toNat < 2 ^ 256
    · rw [Nat.mod_eq_of_lt hs]
      omega
    · have hn : a.toNat + b.toNat - 2 ^ 256 < 2 ^ 256 := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hn]
      omega
  simp only [he]

theorem unsignedSubTest_raw (a b : Word) (tail : Stack) :
    run unsignedSubTest (a :: b :: tail) =
      some (flag (decide (a.toNat < b.toNat)) :: a :: b :: tail) := rfl

/-- The real ADD test is exactly the complement of the intrinsic range predicate. -/
theorem unsignedAddTest_typed (a b : PrimTy.uint.Denote) (tail : Stack) :
    run unsignedAddTest (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (flag (!PrimTy.uint.inRange (a.val + b.val)) ::
        encodeValue .uint a :: encodeValue .uint b :: tail) := by
  rw [unsignedAddTest_raw, encode_uint_toNat, encode_uint_toNat]
  have ha : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a
  have hb : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b
  have he : decide (2 ^ 256 ≤ a.val.toNat + b.val.toNat) =
      !PrimTy.uint.inRange (a.val + b.val) := by
    by_cases hr : PrimTy.uint.inRange (a.val + b.val) = true
    · have hrr : 0 ≤ a.val + b.val ∧ a.val + b.val < ((2 ^ 256 : Nat) : Int) := by
        simpa only [PrimTy.inRange, decide_eq_true_eq] using hr
      have hc : ¬ (2 ^ 256 ≤ a.val.toNat + b.val.toNat) := by omega
      simp only [hc, decide_false, hr, Bool.not_true]
    · have hrr : ¬ (0 ≤ a.val + b.val ∧ a.val + b.val < ((2 ^ 256 : Nat) : Int)) := by
        simpa only [PrimTy.inRange, decide_eq_true_eq] using hr
      have hc : 2 ^ 256 ≤ a.val.toNat + b.val.toNat := by omega
      have hrf : PrimTy.uint.inRange (a.val + b.val) = false := Bool.eq_false_iff.mpr hr
      simp only [hc, decide_true, hrf, Bool.not_false]
  rw [he]

theorem unsignedSubTest_typed (a b : PrimTy.uint.Denote) (tail : Stack) :
    run unsignedSubTest (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (flag (!PrimTy.uint.inRange (a.val - b.val)) ::
        encodeValue .uint a :: encodeValue .uint b :: tail) := by
  rw [unsignedSubTest_raw, encode_uint_toNat, encode_uint_toNat]
  have ha : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a
  have hb : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b
  have he : decide (a.val.toNat < b.val.toNat) =
      !PrimTy.uint.inRange (a.val - b.val) := by
    by_cases hr : PrimTy.uint.inRange (a.val - b.val) = true
    · have hrr : 0 ≤ a.val - b.val ∧ a.val - b.val < ((2 ^ 256 : Nat) : Int) := by
        simpa only [PrimTy.inRange, decide_eq_true_eq] using hr
      have hc : ¬ (a.val.toNat < b.val.toNat) := by omega
      simp only [hc, decide_false, hr, Bool.not_true]
    · have hrr : ¬ (0 ≤ a.val - b.val ∧ a.val - b.val < ((2 ^ 256 : Nat) : Int)) := by
        simpa only [PrimTy.inRange, decide_eq_true_eq] using hr
      have hc : a.val.toNat < b.val.toNat := by omega
      have hrf : PrimTy.uint.inRange (a.val - b.val) = false := Bool.eq_false_iff.mpr hr
      simp only [hc, decide_true, hrf, Bool.not_false]
  rw [he]

def checkedUintAdd : CheckedCertificate .add .uint rfl where
  test := unsignedAddTest
  body := [.op .ADD]
  correct := by
    intro a b tail
    simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some]
    change guarded unsignedAddTest [.op .ADD] overflowFailure _ =
      some (checkedOutcome .uint (PrimTy.uint.ofInt? (a.val + b.val)) tail)
    apply guarded_range_correct _ _ a b (a.val + b.val) tail (unsignedAddTest_typed a b tail)
    change some ((BitVec.ofInt 256 a.val + BitVec.ofInt 256 b.val) :: tail) = _
    rw [← BitVec.ofInt_add]

def checkedUintSub : CheckedCertificate .sub .uint rfl where
  test := unsignedSubTest
  body := [.op .SUB]
  correct := by
    intro a b tail
    simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some]
    change guarded unsignedSubTest [.op .SUB] overflowFailure _ =
      some (checkedOutcome .uint (PrimTy.uint.ofInt? (a.val - b.val)) tail)
    apply guarded_range_correct _ _ a b (a.val - b.val) tail (unsignedSubTest_typed a b tail)
    change some ((BitVec.ofInt 256 a.val - BitVec.ofInt 256 b.val) :: tail) = _
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

example : guarded unsignedAddTest [.op .ADD] overflowFailure
    [BitVec.ofInt 256 (-1), 1, 99] = some (.error overflowFailure) := rfl
example : guarded unsignedSubTest [.op .SUB] overflowFailure [3, 7, 99] =
    some (.error overflowFailure) := rfl
example : guarded unsignedAddTest [.op .ADD] overflowFailure [3, 7, 99] =
    some (.ok [10, 99]) := rfl

#print axioms checkedUintAdd
#print axioms checkedUintSub

end Solidity.Backend.Scalar
