import Solidity.Lowering.V08.SelectorObservations

/-! Kernel controls on the existing selector definitions; no collision axiom. -/
namespace Solidity.Lowering.V08.SelectorControls
open Solidity

/-- Concrete UTF-8 inputs checked by kernel conversion, before hash reduction. -/
theorem error_input : "Error(string)".toUTF8.toList.map UInt8.toNat =
    [69, 114, 114, 111, 114, 40, 115, 116, 114, 105, 110, 103, 41] := by
  change ((⟨#[69, 114, 114, 111, 114, 40, 115, 116, 114, 105, 110, 103, 41]⟩ : ByteArray).toList.map UInt8.toNat) = _
  have size : (⟨#[69, 114, 114, 111, 114, 40, 115, 116, 114, 105, 110, 103, 41]⟩ : ByteArray).size = 13 := rfl
  unfold ByteArray.toList
  repeat' (rw [ByteArray.toList.loop]; simp only [size, Nat.reduceLT, Nat.reduceAdd, if_true, if_false])
  rfl

theorem panic_input : "Panic(uint256)".toUTF8.toList.map UInt8.toNat =
    [80, 97, 110, 105, 99, 40, 117, 105, 110, 116, 50, 53, 54, 41] := by
  change ((⟨#[80, 97, 110, 105, 99, 40, 117, 105, 110, 116, 50, 53, 54, 41]⟩ : ByteArray).toList.map UInt8.toNat) = _
  have size : (⟨#[80, 97, 110, 105, 99, 40, 117, 105, 110, 116, 50, 53, 54, 41]⟩ : ByteArray).size = 14 := rfl
  unfold ByteArray.toList
  repeat' (rw [ByteArray.toList.loop]; simp only [size, Nat.reduceLT, Nat.reduceAdd, if_true, if_false])
  rfl

/-- Existing canonical Error and Panic signature observations remain distinct. -/
theorem distinct_signatures : Source.selector "Error(string)" ≠ Source.selector "Panic(uint256)" := by
  rw [SelectorObservations.signature_selector, SelectorObservations.signature_selector]
  unfold Semantics.customSelector Keccak.selector Keccak.keccak256Str
  rw [error_input, panic_input]
  decide +kernel

/-- Actual selector bytes match the pinned standard Error selector. -/
theorem canonical_error : Semantics.selectorBytes (Semantics.customSelector "Error(string)") =
    Source.errorSelector := by
  unfold Semantics.customSelector Keccak.selector Keccak.keccak256Str
  rw [error_input]
  decide +kernel

/-- Distinct scalar argument order is observable after any selector prefix. -/
theorem argument_order (selector : List UInt8) :
    selector ++ (Semantics.wordBytes 1 ++ Semantics.wordBytes 2) ≠
      selector ++ (Semantics.wordBytes 2 ++ Semantics.wordBytes 1) := by
  intro same
  have rest := List.append_cancel_left same
  exact (by decide +kernel : Semantics.wordBytes 1 ++ Semantics.wordBytes 2 ≠
    Semantics.wordBytes 2 ++ Semantics.wordBytes 1) rest

#print axioms error_input
#print axioms panic_input
#print axioms distinct_signatures
#print axioms canonical_error
#print axioms argument_order
end Solidity.Lowering.V08.SelectorControls
