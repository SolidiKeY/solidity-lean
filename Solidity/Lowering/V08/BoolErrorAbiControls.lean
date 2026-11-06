import Solidity.Lowering.V08.BoolErrorAbi
import Solidity.Lowering.V08.BoolErrorControls

namespace Solidity.Lowering.V08.BoolErrorAbiControls
open Solidity Source Backend BoolErrorAbi BoolErrorControls SourceCustomErrorControls

/-- Actual populated Source run, with independent indexed-codec bytes. -/
def source_client (pipeline : Roadmap.Pipeline) :=
 source_typed (global pipeline) frame 0 (declaration 3) bits typed_three caller populated

/-- Exact selected target endpoint and full reached-memory byte observation. -/
def target_client (pipeline : Roadmap.Pipeline) :=
 packet_readback (Γ:=SourceExternalPhaseControls.ctx) (global pipeline) 8
 (declaration 3) bits typed_three suffix machine (fits pipeline) (by decide +kernel)

theorem bool_two_refused : AbiEntry.Kind.bool.valid 2 = false := by decide +kernel
theorem zero_word : (word false).val = 0 := rfl
theorem one_word : (word true).val = 1 := rfl

theorem wrong_order : AbiEntry.encodeArgs (values bits) ≠
 AbiEntry.encodeArgs (values [false,true,true]) := by
 rw [← encoding_agreement, ← encoding_agreement]
 exact BoolErrorControls.wrong_order_encoded

theorem missing_word : AbiEntry.encodeArgs (values [true]) ≠ [] := by decide +kernel

/-- Test-only lossless decimal-byte rendering; this is not a codec. -/
def render (bs : List UInt8) : String :=
 "[" ++ String.intercalate "," (bs.map (fun b => toString b.toNat)) ++ "]"

def samples : List (List Bool) := [[],[false],[true],[true,false,true],[false,true,true]]
#eval String.intercalate "\n" (samples.map (fun bs => render (BoolErrorLowering.encoded bs)))
#eval String.intercalate "\n" (samples.map (fun bs => render (AbiEntry.encodeArgs (values bs))))

#print axioms word_bytes
#print axioms static_go
#print axioms encoding_agreement
#print axioms payload_agreement
#print axioms source_typed
#print axioms packet_readback
#print axioms source_client
#print axioms target_client
#print axioms bool_two_refused
#print axioms wrong_order
#print axioms missing_word
end Solidity.Lowering.V08.BoolErrorAbiControls
