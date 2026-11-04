import Solidity.Backend.Selection.ScalarSequenceFrames
import Solidity.Backend.Selection.ScalarSequenceControls

/-! Actual V2 consumers with nonempty protected tails and rejection of an
internal overflow despite a fitting final height. No runtime producer is used. -/
namespace Solidity.Backend.Selection.ScalarSequenceFrameControls
open Scalar ScalarSequence ScalarSequenceControls

def certified : V2.FrameCertificate (frameTail caller [])
    (encodeValue .bool false :: encodeValue .int negative :: frameTail caller []) :=
  boundedFrame caller [] (by decide) a b wrapped negative true rfl rfl rfl rfl

def checkedCertified : V2.FrameCertificate (frameTail caller [])
    (0 :: 3 :: 5 :: 0 :: encodeValue .int negative :: frameTail caller []) :=
  boundedCheckedFrame caller [] (by decide) a b wrapped negative true rfl rfl rfl rfl

/-- The actual certificates admit a nonempty physical suffix. -/
theorem protected_tail :
    run certified.code (frameTail caller [] ++ [23,41]) =
      some (encodeValue .bool false :: encodeValue .int negative ::
        (frameTail caller [] ++ [23,41])) ∧
    stackBound certified.code ((frameTail caller [] ++ [23,41]).length : Int) = true :=
  ⟨certified.frame [23,41], certified.capacity [23,41] (by decide)⟩

theorem checked_protected_tail :
    run checkedCertified.code (frameTail caller [] ++ [23,41]) =
      some (0 :: 3 :: 5 :: 0 :: encodeValue .int negative ::
        (frameTail caller [] ++ [23,41])) ∧
    stackBound checkedCertified.code
      ((frameTail caller [] ++ [23,41]).length : Int) = true :=
  ⟨checkedCertified.frame [23,41], checkedCertified.capacity [23,41] (by decide)⟩

/-- A corrupted protected word is excluded by the real run, not only length. -/
theorem reject_corrupted_tail :
    run certified.code (frameTail caller [] ++ [23,41]) ≠
      some (encodeValue .bool false :: encodeValue .int negative ::
        (frameTail caller [] ++ [23,40])) := by
  rw [protected_tail.1]
  decide

/-- Final height 1024 cannot hide the base sequence's intermediate 1025. -/
theorem reject_base_peak (output : Stack)
    (c : V2.FrameCertificate (frameTail caller (List.replicate 1020 0)) output)
    (sameCode : c.code = code a b) : False := by
  have capacity : stackBound c.code
      ((frameTail caller (List.replicate 1020 0)).length : Int) = true :=
    c.capacity_empty
  rw [sameCode] at capacity
  have bound : 0 ≤ ((frameTail caller (List.replicate 1020 0)).length : Int) ∧
      ((frameTail caller (List.replicate 1020 0)).length : Int) + 3 ≤ 1024 :=
    (capacity_iff a b _).mp capacity
  simp only [frame_length, List.length_replicate] at bound
  omega

/-- The checked sequence's +6 peak is enforced independently of its output. -/
theorem reject_checked_peak (output : Stack)
    (c : V2.FrameCertificate (frameTail caller (List.replicate 1017 0)) output)
    (sameCode : c.code = checkedCode a b) : False := by
  have capacity : stackBound c.code
      ((frameTail caller (List.replicate 1017 0)).length : Int) = true :=
    c.capacity_empty
  rw [sameCode] at capacity
  have bound : 0 ≤ ((frameTail caller (List.replicate 1017 0)).length : Int) ∧
      ((frameTail caller (List.replicate 1017 0)).length : Int) + 6 ≤ 1024 :=
    (checked_capacity_iff a b _).mp capacity
  simp only [frame_length, List.length_replicate] at bound
  omega

#print axioms protected_tail
#print axioms checked_protected_tail
#print axioms reject_corrupted_tail
#print axioms reject_base_peak
#print axioms reject_checked_peak

end Solidity.Backend.Selection.ScalarSequenceFrameControls
