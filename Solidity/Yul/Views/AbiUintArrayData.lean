import Solidity.Yul.Views.AbiWordInput

namespace Solidity.Yul.Views

/-- Actual ABI coordinates, preserving the owner's arbitrary byte offset. -/
def abiArrayOffset (input : Roadmap.Bytes) (head : Nat) : Nat := Source.wordAt input head
def abiArrayLength (input : Roadmap.Bytes) (head : Nat) : Nat := Source.wordAt (input.drop (abiArrayOffset input head)) 0
def abiArrayPayload (input : Roadmap.Bytes) (head : Nat) : Roadmap.Bytes := input.drop (abiArrayOffset input head+32)

/-- Actual intrinsically typed scalar values, not an untyped decoded IR. -/
def abiUintValues (D : Source.Layout) (payload : Roadmap.Bytes) (n : Nat) : List (Source.Val D (.int Source.IntTy.u256)) :=
  (List.range n).map (fun j => uintValueOfWord D (abiInputWord payload j))

def abiUintArrayData (D : Source.Layout) (payload : Roadmap.Bytes) (n : Nat) :
    Source.Data D (.array .memory (.int Source.IntTy.u256) none) :=
  let xs := abiUintValues D payload n
  .array xs.length (fun _ h => nomatch h) (fun i => .val (xs.get i))

theorem abiUintValues_length (D : Source.Layout) (payload : Roadmap.Bytes) (n : Nat) :
    (abiUintValues D payload n).length=n := by
  simp only [abiUintValues,List.length_map,List.length_range]

/-- The owner EM lift and left-to-right mapM decode EXACTLY these values.
There is no array allocation while elements are being decoded. -/
theorem abiUintValues_mapM {E Γ} (payload : Roadmap.Bytes) (n : Nat) :
    ((List.range n).mapM (fun j => (Source.EM.lift
      (Source.decodeWord E.layout (Source.wordAt payload j) (.int Source.IntTy.u256)) :
        Source.EM E Γ (Source.Val E.layout (.int Source.IntTy.u256))))) = pure (abiUintValues E.layout payload n) := by
  have each : (fun j => (Source.EM.lift (Source.decodeWord E.layout (Source.wordAt payload j) (.int Source.IntTy.u256)) :
      Source.EM E Γ (Source.Val E.layout (.int Source.IntTy.u256))))=
      (fun j => pure (uintValueOfWord E.layout (abiInputWord payload j))) := by
    funext j
    rw [abi_decode_uint_input]
    rfl
  rw [each,List.mapM_pure]
  rfl

theorem abiUintArrayData_inner {E : Source.Env} (payload : Roadmap.Bytes) (n : Nat) :
    Source.Data.Inner (E := E) (abiUintArrayData E.layout payload n) := fun _ => ⟨_,rfl⟩

theorem abiUintArrayData_valid (E : Source.Env) (H : Source.HeapTy) (payload : Roadmap.Bytes) (n : Nat) :
    Source.DataOK E H (abiUintArrayData E.layout payload n) :=
  .array (fun _ => .val (Source.Val.refOK_of_loc rfl _))

theorem abiUintArrayData_shape (D : Source.Layout) (payload : Roadmap.Bytes) (n : Nat) :
    HasMemoryShape (abiUintArrayData D payload n) (.array true (abiUintValues D payload n).length) := .array _ _ _

end Solidity.Yul.Views
