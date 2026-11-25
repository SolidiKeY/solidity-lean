import Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip.Leaves

/-! Checks of the function-signature round trip's leaf facts. Every reading
here is a kernel proof (no `#guard`, no native code). -/
namespace Solidity.Examples.Lowering.Total.FunctionTypeRoundTrip

open Solidity Solidity.Correctness.Lowering.Total
open Solidity.Correctness.Lowering.Total.FunctionTypeDecode
open Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip

def u256 : Source.Elem := .int false 256 (by decide)

/-! ## Core string reading in the kernel -/

example : ("0042" : String).toNat? = some 42 := (toNat?_mk _).trans (by decide)
example : ("4x" : String).toNat? = none := (toNat?_mk _).trans (by decide)
example : narrowTy? "int48" = some (.int, 48) := (narrowTy?_mk _).trans (by decide)
example : bytesTy? "bytes32" = some 32 ∧ bytesTy? "bytes33" = none :=
  ⟨(bytesTy?_mk _).trans (by decide), (bytesTy?_mk _).trans (by decide)⟩

/-! ## Elementary leaves: every width -/

example (s : Bool) (bits : Nat) (h) : leaf (elemName (.int s bits h)) = .elem (.int s bits h) :=
  (spelled_leaf (e := .int s bits h) trivial).1
example (n : Nat) (h) : leaf (elemName (.fixedBytes n h)) = .elem (.fixedBytes n h) ∧
    fnTy? (elemName (.fixedBytes n h)) = false :=
  have l := spelled_leaf (e := .fixedBytes n h) trivial
  ⟨l.1, l.2.1⟩
/-- `address payable` has no spelling of its own. -/
example : ¬ Spelled .addressPayable ∧ elemName .addressPayable = "" := ⟨id, rfl⟩

/-! ## Names: the elementary condition -/

example : ElemFree "S" ∧ ElemFree "uint7" ∧ ElemFree "mapping(uint=>bool)" := by decide +kernel
/-- `uint256` is a name of `uint`. -/
example : ¬ ElemFree "uint256" ∧ leaf "uint256" = .elem u256 :=
  ⟨by decide +kernel, (leaf_mk _).trans (by decide +kernel)⟩
example : ElemFree "Point[]" := elemFree_of_last (by decide) (by decide)

/-! ## Locations: cut at the spelled one -/

example (b : String) (d : Source.DataLoc) : leaf (b ++ locName d) = .located b d := leaf_located b d
/-- The boundary is not recorded: the name `Tmemory` reads as `T` in memory. -/
example : leaf "Tmemory" = .located "T" .memory := leaf_located "T" .memory
example : leaf "Tmemorystorage" = .located "Tmemory" .storage := leaf_located "Tmemory" .storage

end Solidity.Examples.Lowering.Total.FunctionTypeRoundTrip
