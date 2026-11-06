import Solidity.Lowering.V08.LiteralFailureSelectorBytes
import Solidity.Lowering.V08.LiteralFailureDynamicListErrorControls

namespace Solidity.Lowering.V08.LiteralFailureSelectorBytesControls
open Solidity Source LiteralFailureDynamicListError
open LiteralFailureDynamicListErrorControls
open LiteralFailureSelectorBytes

def caller (bytes : Roadmap.Bytes) (extent : bytes.length = 4) :
 Locals (environment 3).layout (Selector :: context) :=
 .cons (.fixedBytes bytes extent) (locals 3)
def tailRefs : List (Source.Idx (Selector :: context) (.bytes .memory)) :=
 [.there .here,.there (.there .here),.there .here]
def packet (selector first second : Roadmap.Bytes) : Roadmap.Bytes :=
 selector ++ AbiEntry.encodeArgs (abiValues [first,second,first])

theorem memory_tail (selector first second : Roadmap.Bytes) (extent : selector.length = 4) :
 all_represented (caller selector extent) (state 3 first second) tailRefs [first,second,first] :=
 ⟨⟨1,rfl,.inl rfl⟩,⟨⟨2,rfl,.inr rfl⟩,⟨⟨1,rfl,.inl rfl⟩,trivial⟩⟩⟩

theorem populated (pipeline : Roadmap.Pipeline) (selector first second : Roadmap.Bytes)
 (extent : selector.length = 4) :
 (evalE (global 3 pipeline) frame 8 (.abiEncode .encodeWithSelector (args .here tailRefs))).run
 (caller selector extent,state 3 first second) =
 (.ok (.val (.memRef rfl 3)),(caller selector extent,
  SourceKeccak.afterLiteral (state 3 first second) (packet selector first second))) :=
 expression_run (global 3 pipeline) frame 0 .here tailRefs [first,second,first]
  (caller selector extent) (state 3 first second) (memory_tail selector first second extent)

theorem only_selector (pipeline : Roadmap.Pipeline) (selector first second : Roadmap.Bytes)
 (extent : selector.length = 4) :
 (evalE (global 3 pipeline) frame 5 (.abiEncode .encodeWithSelector (args .here []))).run
 (caller selector extent,state 3 first second) =
 (.ok (.val (.memRef rfl 3)),(caller selector extent,
  SourceKeccak.afterLiteral (state 3 first second) selector)) := by
 have execution := expression_run (global 3 pipeline) frame 0 .here [] []
  (caller selector extent) (state 3 first second) trivial
 simpa only [caller,Locals.get,Source.Val.bytesOf,abiValues,AbiEntry.encodeArgs,
  AbiEntry.Vals.parts,AbiEntry.assemble,AbiEntry.assemble.go,List.foldl_nil,List.append_nil] using execution

theorem selector_projection (selector first second : Roadmap.Bytes) (extent : selector.length = 4) :
 (packet selector first second).take 4 = selector :=
 prefix_readback (Source.Val.fixedBytes (D := (environment 3).layout) (h := by decide +kernel) selector extent) _

theorem body_projection (selector first second : Roadmap.Bytes) (extent : selector.length = 4) :
 (packet selector first second).drop 4 = AbiEntry.encodeArgs (abiValues [first,second,first]) :=
 body_readback (Source.Val.fixedBytes (D := (environment 3).layout) (h := by decide +kernel) selector extent) _

theorem fresh_output (selector first second : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state 3 first second) (packet selector first second)).heap.get 3 =
 some ⟨.bytes .memory,.bytes (packet selector first second)⟩ := SourceKeccak.allocated _ _

theorem older_survives (selector first second : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state 3 first second) (packet selector first second)).heap.get 0 =
 some ⟨.bytes .memory,.bytes [9,7]⟩ := LiteralFailureSignatureBytes.object_preserved _ _ _ _ rfl

theorem wrong_offset :
 ((packet [0,255,128,1] [0,255] [128]).drop 4).take 32 ≠ AbiEntry.wordBytes 32 := by decide +kernel

theorem changed_selector : packet [0,255,128,1] [0,255] [128] ≠
 packet [1,255,128,1] [0,255] [128] := by decide +kernel

theorem no_argument_fuel (pipeline : Roadmap.Pipeline) (selector first second : Roadmap.Bytes)
 (extent : selector.length = 4) :
 (evalE (global 3 pipeline) frame 1 (.abiEncode .encodeWithSelector (args .here tailRefs))).run
 (caller selector extent,state 3 first second) =
 (.error .timeout,(caller selector extent,state 3 first second)) := by rfl

def observations : List Roadmap.Bytes :=
 [[0,0,0,0],packet [222,173,190,239] [] [],packet [0,255,128,1] [0,255] [128],
  packet [255,0,255,0] (List.replicate 31 0) [],
  packet [1,2,3,4] (List.replicate 32 255) (List.replicate 33 128),
  packet [4,3,2,1] (List.replicate 33 128) (List.replicate 32 255)]
#eval String.intercalate "\n" (observations.map render)
#print axioms Solidity.Lowering.V08.LiteralFailureSelectorBytes.arguments_run
#print axioms selector_extent
#print axioms conversion_run
#print axioms expression_run
#print axioms prefix_readback
#print axioms body_readback
#print axioms memory_tail
#print axioms populated
#print axioms only_selector
#print axioms selector_projection
#print axioms body_projection
#print axioms fresh_output
#print axioms older_survives
#print axioms wrong_offset
#print axioms changed_selector
#print axioms no_argument_fuel
end Solidity.Lowering.V08.LiteralFailureSelectorBytesControls
