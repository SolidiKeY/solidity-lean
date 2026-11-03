import Solidity.Lowering.V08.LiteralFailurePackedBytes
import Solidity.Lowering.V08.LiteralFailureDynamicListErrorControls

namespace Solidity.Lowering.V08.LiteralFailurePackedBytesControls
open Solidity Source LiteralFailureDynamicListError
open LiteralFailureDynamicListErrorControls

theorem populated (pipeline : Roadmap.Pipeline) (first second : Roadmap.Bytes) :
 (evalE (global 3 pipeline) frame 7 (.abiEncode .encodePacked (LiteralFailurePackedBytes.args refs))).run
  (locals 3,state 3 first second) =
 (.ok (.val (.memRef rfl 3)),(locals 3,
  {state 3 first second with heap := ((state 3 first second).heap.alloc
   ⟨.bytes .memory,.bytes (first ++ second ++ first)⟩).1})) := by
 simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc] using
  LiteralFailurePackedBytes.expression_run (global 3 pipeline) frame 0 refs
   [first,second,first] (locals 3) (state 3 first second) (memory_three first second)

theorem fresh_output (first second : Roadmap.Bytes) :
 let heap := ((state 3 first second).heap.alloc
   ⟨.bytes .memory,.bytes (first ++ second ++ first)⟩).1
 heap.get 3 = some ⟨.bytes .memory,.bytes (first ++ second ++ first)⟩ ∧
 heap.get 0 = some ⟨.bytes .memory,.bytes [9,7]⟩ ∧ heap.next = 4 := by
 exact ⟨rfl,rfl,rfl⟩

/-- Packed bytes are intentionally not delimiter-injective. -/
theorem collision : ([[1],[2]] : List Roadmap.Bytes).flatten = [[],[1,2]].flatten := by rfl

theorem ordinary_distinguishes :
 AbiEntry.encodeArgs (abiValues [[1],[2]]) ≠ AbiEntry.encodeArgs (abiValues [[],[1,2]]) := by
 decide +kernel

theorem not_padded : ([[0,255],[128],[0,255]] : List Roadmap.Bytes).flatten ≠
 AbiEntry.encodeArgs (abiValues [[0,255],[128],[0,255]]) := by decide +kernel

def packets : List (List Roadmap.Bytes) :=
 [[],[[0,255]],[[0,255],[128],[0,255]],[List.replicate 31 0],
  [List.replicate 32 255],[List.replicate 33 128]]
#eval String.intercalate "\n" (packets.map (fun p => render p.flatten))
#print axioms LiteralFailurePackedBytes.packed_parts
#print axioms LiteralFailurePackedBytes.part_run
#print axioms LiteralFailurePackedBytes.parts_run
#print axioms LiteralFailurePackedBytes.encoding_run
#print axioms LiteralFailurePackedBytes.args_run
#print axioms LiteralFailurePackedBytes.expression_run
#print axioms populated
#print axioms fresh_output
#print axioms collision
#print axioms ordinary_distinguishes
#print axioms not_padded
end Solidity.Lowering.V08.LiteralFailurePackedBytesControls
