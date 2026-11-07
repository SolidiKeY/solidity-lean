import Solidity.Backend.AbiEntry.WordValidationInterface
import Solidity.Backend.Scalar.UnsignedMul
import Solidity.Backend.Selection.InterfaceV2

/-! Concrete primitive ABI word validation in the existing gasless numeric
runner. Unsigned bounds at or above 2^256 accept every word without truncating
the immediate. Signed and fixed-bytes validation preserve the exact semantic
predicates. This does not execute calldata loading or runtime dispatch. -/
namespace Solidity.Backend.AbiEntry.WordValidation
open Scalar

/-- Compare a loaded word with an unbounded semantic bound. -/
def belowCode (bound : Nat) : Program :=
  if bound < 2 ^ 256 then
    [pushWord (BitVec.ofNat 256 bound), .op .GT]
  else [.op .POP, pushByte 1]

theorem below_correct (bound : Nat) (word : Scalar.Word) (tail : Stack) :
    run (belowCode bound) (word :: tail) =
      some (flag (decide (word.toNat < bound)) :: tail) := by
  by_cases hb : bound < 2 ^ 256
  · rw [belowCode, if_pos hb, run, step_pushWord]
    simp only [run, step, numericStep, unary, binary, applyBinary,
      Option.bind_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  · have hw : word.toNat < bound := Nat.lt_of_lt_of_le word.isLt (Nat.le_of_not_gt hb)
    rw [belowCode, if_neg hb]
    change some (1 :: tail) = some (flag (decide (word.toNat < bound)) :: tail)
    simp only [decide_eq_true hw, flag, if_true]

theorem below_capacity (bound : Nat) (tail : Stack)
    (h : tail.length + 2 ≤ 1024) :
    stackBound (belowCode bound) ((tail.length + 1 : Nat) : Int) = true := by
  unfold belowCode
  split <;>
    simp only [stackBound, heightTrace, stackDelta, pushWord, pushByte,
      numericDelta, unary, binary, Option.isSome_some, if_true,
      List.all_cons, List.all_nil, Bool.and_true, safeHeight,
      Bool.and_eq_true, decide_eq_true_eq] <;> omega

/-- The semantic enum bound is kept at its actual cardinality. -/
def enumValidator (members : Nat) : Interface.WordValidator (.enumBelow members) where
  code := belowCode members
  scratch := 1
  scratch_fits := by decide
  correct := below_correct members
  capacity := below_capacity members

/-- Boolean validation rejects every word other than zero and one. -/
def boolValidator : Interface.WordValidator .bool where
  code := belowCode 2
  scratch := 1
  scratch_fits := by decide
  correct := below_correct 2
  capacity := below_capacity 2

/-- Covers arbitrary bit counts, including the full word and address160. -/
def uintValidator (bits : Nat) : Interface.WordValidator (.uint bits) where
  code := belowCode (2 ^ bits)
  scratch := 1
  scratch_fits := by decide
  correct := below_correct (2 ^ bits)
  capacity := below_capacity (2 ^ bits)

/-- Keep one copy for each signed bound; reject dirty sign-extension bits. -/
def signedCode (bits : Nat) : Program :=
  [.op (.DUP ⟨0, by decide⟩)] ++ (belowCode (2 ^ (bits - 1)) ++
  ([.op (.SWAP ⟨0, by decide⟩)] ++
  (belowCode (Solidity.AbiEntry.W - 2 ^ (bits - 1)) ++ [.op .ISZERO, .op .OR])))

theorem signed_correct (bits : Nat) (word : Scalar.Word) (tail : Stack) :
    run (signedCode bits) (word :: tail) =
      some (flag ((Solidity.AbiEntry.Kind.int bits).valid word.toNat) :: tail) := by
  rw [signedCode, run_append]
  change run (belowCode (2 ^ (bits - 1)) ++ _) (word :: word :: tail) = _
  rw [run_append, below_correct]
  change run ([.op (.SWAP ⟨0, by decide⟩)] ++
      (belowCode (Solidity.AbiEntry.W - 2 ^ (bits - 1)) ++ [.op .ISZERO, .op .OR]))
      (flag (decide (word.toNat < 2 ^ (bits - 1))) :: word :: tail) = _
  rw [run_append]
  change run (belowCode (Solidity.AbiEntry.W - 2 ^ (bits - 1)) ++ [.op .ISZERO, .op .OR])
      (word :: flag (decide (word.toNat < 2 ^ (bits - 1))) :: tail) = _
  rw [run_append, below_correct]
  change some ((flag (flag (decide (word.toNat < Solidity.AbiEntry.W - 2 ^ (bits - 1))) == 0)
      ||| flag (decide (word.toNat < 2 ^ (bits - 1)))) :: tail) = _
  rw [flag_iszero, flag_or, Bool.or_comm, ← decide_not]
  simp only [Nat.not_lt, Solidity.AbiEntry.Kind.valid]

theorem signed_capacity (bits : Nat) (tail : Stack) (h : tail.length + 3 ≤ 1024) :
    stackBound (signedCode bits) ((tail.length + 1 : Nat) : Int) = true := by
  by_cases lo : 2 ^ (bits - 1) < 2 ^ 256 <;>
    by_cases hi : Solidity.AbiEntry.W - 2 ^ (bits - 1) < 2 ^ 256 <;>
    simp only [signedCode, belowCode, lo, hi, if_true, if_false,
      List.cons_append, List.nil_append, stackBound, heightTrace, stackDelta,
      pushWord, pushByte, numericDelta, unary, binary, Option.isSome_some, Option.isSome_none,
      List.all_cons, List.all_nil, Bool.and_true, safeHeight,
      Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] <;> omega

def signedValidator (bits : Nat) : Interface.WordValidator (.int bits) where
  code := signedCode bits
  scratch := 2
  scratch_fits := by decide
  correct := signed_correct bits
  capacity := signed_capacity bits

/-- bytesN is left-aligned; validate its low padding bits without cleanup. -/
def bytesCode (size : Nat) : Program :=
  [pushWord (BitVec.ofNat 256 (2 ^ (256 - 8 * size) - 1)), .op .AND, .op .ISZERO]

theorem bytes_correct (size : Nat) (word : Scalar.Word) (tail : Stack) :
    run (bytesCode size) (word :: tail) =
      some (flag ((Solidity.AbiEntry.Kind.fixedBytes size).valid word.toNat) :: tail) := by
  have hp : 2 ^ (256 - 8 * size) ≤ 2 ^ 256 :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hm : 2 ^ (256 - 8 * size) - 1 < 2 ^ 256 := by
    have positive : 0 < 2 ^ (256 - 8 * size) := Nat.pow_pos (by decide)
    omega
  have normalized : (BitVec.ofNat 256 (2 ^ (256 - 8 * size) - 1) &&& word).toNat =
      word.toNat % 2 ^ (256 - 8 * size) := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm,
      Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  have zero_word : (0 : Scalar.Word).toNat = 0 := rfl
  have zero : ((BitVec.ofNat 256 (2 ^ (256 - 8 * size) - 1) &&& word) == 0) =
      (word.toNat % 2 ^ (256 - 8 * size) == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro equal
      simpa only [normalized, zero_word] using congrArg BitVec.toNat equal
    · intro equal
      apply BitVec.eq_of_toNat_eq
      rw [normalized, equal]
      rfl
  rw [bytesCode, run, step_pushWord]
  change some (flag ((BitVec.ofNat 256 (2 ^ (256 - 8 * size) - 1) &&& word) == 0) :: tail) = _
  rw [zero]
  rfl

theorem bytes_capacity (size : Nat) (tail : Stack) (h : tail.length + 2 ≤ 1024) :
    stackBound (bytesCode size) ((tail.length + 1 : Nat) : Int) = true := by
  simp only [bytesCode, stackBound, heightTrace, stackDelta, pushWord,
    numericDelta, unary, binary, Option.isSome_some, Option.isSome_none,
    List.all_cons, List.all_nil, Bool.and_true, safeHeight,
    Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq, if_false, if_true]
  omega

def bytesValidator (size : Nat) : Interface.WordValidator (.fixedBytes size) where
  code := bytesCode size
  scratch := 1
  scratch_fits := by decide
  correct := bytes_correct size
  capacity := bytes_capacity size

/-- Every semantic word kind has concrete validation, without input exclusions. -/
def validator : (kind : Solidity.AbiEntry.Kind) → Interface.WordValidator kind
  | .uint bits => uintValidator bits
  | .int bits => signedValidator bits
  | .bool => boolValidator
  | .fixedBytes size => bytesValidator size
  | .enumBelow members => enumValidator members

/-- Export actual validator code through the non-vacuous physical frame V2.
The predicate flag replaces the loaded word; callers retain arbitrary suffixes. -/
def frameCertificate (kind : Solidity.AbiEntry.Kind)
    (validation : Interface.WordValidator kind) (word : Scalar.Word) :
    Selection.V2.FrameCertificate [word] [flag (kind.valid word.toNat)] where
  code := validation.code
  peak := validation.scratch
  inputRoom := validation.scratch_fits
  frame := validation.correct word
  capacity := by
    intro tail room
    simp only [List.cons_append, List.nil_append, List.length_cons] at room ⊢
    exact validation.capacity tail room

namespace Checks

theorem signed_edges :
    run (signedCode 8) [127, 9] = some [1, 9] ∧
    run (signedCode 8) [128, 9] = some [0, 9] ∧
    run (signedCode 8) [BitVec.ofNat 256 (2^256-128), 9] = some [1, 9] ∧
    run (signedCode 8) [BitVec.ofNat 256 (2^256-129), 9] = some [0, 9] := by decide +kernel

theorem signed_full :
    run (signedCode 256) [BitVec.ofNat 256 (2^256-1)] = some [1] ∧
    run (signedCode 257) [BitVec.ofNat 256 (2^256-1)] = some [1] := by decide +kernel

theorem bytes_edges :
    run (bytesCode 1) [BitVec.ofNat 256 (171 * 2^248), 9] = some [1, 9] ∧
    run (bytesCode 1) [BitVec.ofNat 256 (171 * 2^248+1), 9] = some [0, 9] ∧
    run (bytesCode 31) [256] = some [1] ∧
    run (bytesCode 31) [257] = some [0] := by decide +kernel

theorem bytes_full :
    run (bytesCode 32) [BitVec.ofNat 256 (2^256-1)] = some [1] ∧
    run (bytesCode 0) [0] = some [1] ∧ run (bytesCode 0) [1] = some [0] := by decide +kernel

theorem capacity_edges :
    stackBound (signedCode 8) 1022 = true ∧ stackBound (signedCode 8) 1023 = false ∧
    stackBound (bytesCode 1) 1023 = true ∧ stackBound (bytesCode 1) 1024 = false := by decide +kernel

theorem factory_cases :
    run (validator (.uint 160)).code [BitVec.ofNat 256 (2^160)] = some [0] ∧
    run (validator .bool).code [1] = some [1] ∧
    run (validator (.enumBelow 3)).code [3] = some [0] ∧
    run (validator (.int 8)).code [127] = some [1] ∧
    run (validator (.fixedBytes 31)).code [257] = some [0] := by decide +kernel

/-- A nontrivial actual V2 frame instance, retaining its concrete code/peak. -/
theorem frame_witness : ∃ certificate : Selection.V2.FrameCertificate [127] [1],
    certificate.code = signedCode 8 ∧ certificate.peak = 2 := by
  exact ⟨frameCertificate (.int 8) (signedValidator 8) 127, rfl, rfl⟩

/-- The actual tail law prevents a fake empty-code certificate here. -/
theorem empty_frame_refused :
    ¬ ∃ certificate : Selection.V2.FrameCertificate [127] [1], certificate.code = [] := by
  rintro ⟨certificate, empty⟩
  have executed : run certificate.code [127] = some [1] := certificate.frame []
  rw [empty] at executed
  have different : (some ([127] : Stack)) ≠ some [1] := by decide
  exact different executed

/-- info: 'Solidity.Backend.AbiEntry.WordValidation.Checks.frame_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frame_witness
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.Checks.empty_frame_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_frame_refused
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.Checks.signed_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed_edges
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.Checks.signed_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed_full
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.Checks.bytes_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_edges
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.Checks.bytes_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_full
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.Checks.capacity_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_edges
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.Checks.factory_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms factory_cases
end Checks

/-- info: 'Solidity.Backend.AbiEntry.WordValidation.frameCertificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frameCertificate
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.signed_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed_correct
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.signed_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed_capacity
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.signedValidator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signedValidator
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.bytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_correct
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.bytes_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_capacity
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.bytesValidator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytesValidator
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.validator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validator

/-- info: 'Solidity.Backend.AbiEntry.WordValidation.below_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms below_correct
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.below_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms below_capacity
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.enumValidator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enumValidator
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.boolValidator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boolValidator
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.uintValidator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uintValidator
end Solidity.Backend.AbiEntry.WordValidation
