import Solidity.Backend.Selection.ScalarSequenceResources

/-! Inhabited typed source, populated caller frame, noncommutative/signed
combination, real DUP peaks and wrong-order/physical-capacity negatives.
All executions here are the published numeric slice, not fetched EVM runs. -/
namespace Solidity.Backend.Selection.ScalarSequenceControls
open Scalar ScalarSequence

def contract : Contract := { vars := [] }
def caller : State contract [.val .int, .val .uint] where
  storage := Storage.init contract
  H := []
  heap := Heap.empty
  env := (⟨-7, by decide⟩, (⟨99, by decide⟩, ()))
def a : PrimTy.uint.Denote := ⟨3, by decide⟩
def b : PrimTy.uint.Denote := ⟨5, by decide⟩
def wrapped : PrimTy.uint.Denote := ⟨Semantics.uintBound - 2, by decide +kernel⟩
def negative : PrimTy.int.Denote := ⟨-2, by decide⟩
def positive : PrimTy.int.Denote := ⟨2, by decide⟩
def two : PrimTy.uint.Denote := ⟨2, by decide⟩

/-- Exact nonempty caller frame and distinct populated protected words. -/
example : frameTail caller [] = [BitVec.ofInt 256 (-7), 99] ∧
    (BitVec.ofInt 256 (-7) : Word) ≠ 99 := ⟨rfl, by decide +kernel⟩

/-- SUB 3-5, reinterpret as signed -2, compare -2<0 and negate. The saved
signed value and both actual typed caller locals remain in the final stack. -/
theorem typed_combination :
    (resultExpr a b).evalT caller = .ok false ∧
    run (code a b) (frameTail caller []) =
      some (0 :: BitVec.ofInt 256 (-2) :: frameTail caller []) ∧
    stackBound (code a b) ((frameTail caller []).length : Int) = true :=
  typed_result caller [] (by decide) a b wrapped negative true rfl rfl rfl rfl rfl

/-- First physical instruction boundary is the right operand above both locals. -/
example : run ((code a b).take 1) (frameTail caller []) = some [5,BitVec.ofInt 256 (-7),99] :=
  first_boundary a b _

/-- Intermediate operand order is left on top, with two distinct caller words. -/
example : run (operands a b) (frameTail caller []) = some [3,5,BitVec.ofInt 256 (-7),99] :=
  (stages (C := contract) (Γ := [.val .int, .val .uint]) a b wrapped negative true
    (frameTail caller []) rfl rfl rfl rfl).1

/-- The DUP/zero preparation really reaches a five-word boundary. -/
example : run (prepared a b) (frameTail caller []) =
    some [0,BitVec.ofInt 256 (-2),BitVec.ofInt 256 (-2),BitVec.ofInt 256 (-7),99] := by
  obtain ⟨_, _, _, _, prepared, _, _, _⟩ := stages (C := contract) (Γ := [.val .int, .val .uint])
    a b wrapped negative true (frameTail caller []) rfl rfl rfl rfl
  exact prepared

/-- Reversing emitted operand order changes both the Boolean and saved value. -/
theorem reverse_order : run (code b a) (frameTail caller []) =
    some (1 :: (2 : Word) :: frameTail caller []) := by
  obtain ⟨_, _, _, _, _, _, _, result⟩ := stages (C := contract) (Γ := [.val .int, .val .uint])
    b a two positive false (frameTail caller []) rfl rfl rfl rfl
  exact result

example : run (code b a) (frameTail caller []) ≠
    some (0 :: BitVec.ofInt 256 (-2) :: frameTail caller []) := by
  rw [reverse_order]
  decide +kernel

/-- All 175 emitted bytes describe the complete base sequence plus the actual
selected overflow test, with no skipped stage or presumed runtime decoder. -/
theorem checked_combination :
    run (checkedCode a b) (frameTail caller []) =
      some (0 :: 3 :: 5 :: 0 :: BitVec.ofInt 256 (-2) :: frameTail caller []) ∧
    stackBound (checkedCode a b) ((frameTail caller []).length : Int) = true ∧
    (Backend.encode (checkedCode a b)).length = 175 ∧
    Backend.decode (Backend.encode (checkedCode a b)) = some (checkedCode a b) :=
  ⟨checked_stages (C := contract) (Γ := [.val .int, .val .uint])
    a b wrapped negative true (frameTail caller []) rfl rfl rfl rfl,
   (checked_frame_capacity_iff caller [] a b).mpr (by decide),
   checked_bytes_length a b, checked_decode_bytes a b⟩

/-- Actual two-DUP2 boundary: eight words, not the seven-word exit. -/
example : run [.op (.DUP 1), .op (.DUP 1)]
    (encodeValue .uint a :: encodeValue .uint b :: 0 :: BitVec.ofInt 256 (-2) :: frameTail caller []) =
    some [3,5,3,5,0,BitVec.ofInt 256 (-2),BitVec.ofInt 256 (-7),99] := rfl

/-- This exact DUP prefix consumes the existing checked-invocation safety law,
with the invocation's room derived from this populated typed frame. -/
example : ([3,5,3,5,0,BitVec.ofInt 256 (-2),BitVec.ofInt 256 (-7),99] : Stack).length ≤ 1024 :=
  checked_prefix_safe caller [] (by decide) a b negative true
    [.op (.DUP 1), .op (.DUP 1)] [.op .ADD, .op (.DUP 1), .op .GT] rfl rfl

/-- Final height 1024 is insufficient: the real intermediate peak is 1025. -/
example : stackBound (code a b) 1022 = false ∧ (1022 + 2 : Nat) ≤ 1024 := by
  refine ⟨Bool.eq_false_iff.mpr ?_, by decide⟩
  intro bad
  have impossible := (capacity_iff a b 1022).mp bad
  omega

/-- The checked sequence likewise fails at its DUP peak although its exit fits. -/
example : stackBound (checkedCode a b) 1019 = false ∧ (1019 + 5 : Nat) ≤ 1024 := by
  refine ⟨Bool.eq_false_iff.mpr ?_, by decide⟩
  intro bad
  have impossible := (checked_capacity_iff a b 1019).mp bad
  omega

/-- Over-capacity is witnessed on this very typed populated frame plus spill. -/
example : stackBound (code a b) ((frameTail caller (List.replicate 1020 0)).length : Int) = false ∧
    (frameTail caller (List.replicate 1020 0)).length + 2 ≤ 1024 := by
  refine ⟨Bool.eq_false_iff.mpr ?_, ?_⟩
  · intro bad
    have impossible := (frame_capacity_iff caller (List.replicate 1020 0) a b).mp bad
    simp only [List.length_replicate] at impossible
    omega
  · rw [frame_length]
    simp only [List.length_replicate]
    decide

example : stackBound (checkedCode a b) ((frameTail caller (List.replicate 1017 0)).length : Int) = false ∧
    (frameTail caller (List.replicate 1017 0)).length + 5 ≤ 1024 := by
  refine ⟨Bool.eq_false_iff.mpr ?_, ?_⟩
  · intro bad
    have impossible := (checked_frame_capacity_iff caller (List.replicate 1017 0) a b).mp bad
    simp only [List.length_replicate] at impossible
    omega
  · rw [frame_length]
    simp only [List.length_replicate]
    decide

/-- Full concrete emitted bytes, including all three PUSH32 payloads. -/
example : Backend.encode (code a b) =
    (0x7f :: List.replicate 31 0 ++ [5]) ++ (0x7f :: List.replicate 31 0 ++ [3]) ++
    [0x03,0x80] ++ (0x7f :: List.replicate 32 0) ++ [0x90,0x12,0x15] := by
  rw [emitted_bytes]
  rfl

/-- Capacity is not inferred from the mere existence of the gasless run. -/
example : ¬ ClosedInvocation
    (subCertificate (C := contract) (Γ := [.val .int, .val .uint]) a b wrapped rfl rfl)
    (List.replicate 1023 0) := by
  intro inv
  have room := inv.prefix_safe (literal .uint b ++ literal .uint a) subChoice.code rfl
    (run_comp (literal_correct .uint b _) (literal_correct .uint a _))
  simp only [List.length_cons, List.length_replicate] at room
  omega

#print axioms typed_combination
#print axioms checked_combination
end Solidity.Backend.Selection.ScalarSequenceControls
