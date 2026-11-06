import Solidity.Lowering.V08.LiteralFailureBytesReadback
import Solidity.Lowering.V08.SourceCustomErrorControls

namespace Solidity.Lowering.V08.LiteralFailureBytesReadbackControls
open Solidity Source Backend LiteralFailureBytesReadback SourceCustomErrorControls

def machine : Failure.Slice.Machine :=
 { stack := [Source.toWord 11,Source.toWord 22], memory := fun _=>165 }
def messages : List (List UInt8) :=
 [[],[0],[255],[0,255],[0,255,128],List.replicate 31 0,List.replicate 32 255,List.replicate 33 128]

/-- Test-local decidability of existing numeric Fits; no profile/default change. -/
local instance (address : Nat) (bs : List UInt8) : Decidable (Failure.Fits address bs) :=
 inferInstanceAs (Decidable (address<Failure.wordLimit ∧ bs.length<Failure.wordLimit ∧ address+bs.length≤Failure.wordLimit))

theorem fits_messages : messages.all (fun bs=>decide (Failure.Fits 8 (errorData bs)))=true := by
 apply List.all_eq_true.mpr
 intro bs member
 simp only [decide_eq_true_eq]
 have sizes : messages.all (fun bs=>decide (bs.length≤33))=true := by decide
 have small : bs.length≤33 := of_decide_eq_true ((List.all_eq_true.mp sizes) bs member)
 have remainder : (32-bs.length%32)%32<32 := Nat.mod_lt _ (by decide)
 have capacity : 200<Failure.wordLimit := by decide
 simp only [Failure.Fits,LiteralFailureLowering.reason_length]
 omega

theorem fits_member (bs : List UInt8) (member : bs∈messages) : Failure.Fits 8 (errorData bs) := by
 exact of_decide_eq_true ((List.all_eq_true.mp fits_messages) bs member)

theorem populated_client (pipeline : Roadmap.Pipeline) (static : Bool)
 (bs : List UInt8) (member : bs∈messages) :
 ∃ code,
  (evalE (global pipeline) {frame with static:=static} 6
   (LiteralFailureLowering.revertReason bs)).run (locals,populated)=
   (.error (.revert (Source.errorSelector ++ AbiEntry.encodeArgs (values bs))),(locals,populated)) ∧
  Failure.Slice.checkedRun code machine=
   some ({machine with memory:=Failure.Slice.putBytes machine.memory 8 (errorData bs)},
    some (revertOutcome (Source.errorSelector ++ AbiEntry.encodeArgs (values bs)))) ∧
  Semantics.decodeError
   (Failure.Slice.getBytes (Failure.Slice.putBytes machine.memory 8 (errorData bs)) 8 (errorData bs).length)=some bs := by
 obtain ⟨code,selected,source,emitted,readback,decoded⟩ :=
  lowered_packet (global pipeline) {frame with static:=static} 0 locals populated bs 8 machine
   (fits_member bs member) (by decide)
 exact ⟨code,source,emitted,decoded⟩

theorem older_byte (bs : List UInt8) :
 Failure.Slice.putBytes machine.memory 8 (errorData bs) 7=165 := by
 exact Failure.Slice.putBytes_frame machine.memory 8 7 (errorData bs) (.inl (by decide))

theorem packet_lengths : messages.map (fun bs=>(errorData bs).length)=[68,100,100,100,100,100,100,132] := by
 rfl

theorem good_reason : Semantics.decodeError (errorData [0,255])=some [0,255] := by
 decide

theorem accepted_unpadded : Semantics.decodeError ((errorData [0,255]).take 70)=some [0,255] := by
 decide

theorem missing_length : Semantics.decodeError ((errorData [0,255]).take 67)=none := by
 decide

theorem truncated_payload : Semantics.decodeError ((errorData [0,255]).take 69)=none := by
 decide

theorem wrong_selector : Semantics.decodeError (0 :: (errorData [0,255]).drop 1)=none := by
 decide

theorem wrong_kind : Semantics.decodePanic (errorData [0,255])=none := by
 decide

theorem wrong_order : Semantics.decodeError (errorData [0,255])≠some [255,0] := by
 decide

/-- Lossless observation serialization only; this does not encode ABI data. -/
def jsonBytes (bs : List UInt8) : String :=
 "[" ++ String.intercalate "," (bs.map (fun b=>toString b.toNat)) ++ "]"
def jsonPackets (packets : List (List UInt8)) : String :=
 "[" ++ String.intercalate "," (packets.map jsonBytes) ++ "]"

end Solidity.Lowering.V08.LiteralFailureBytesReadbackControls

#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.fits_messages
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.fits_member
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.populated_client
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.older_byte
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.packet_lengths
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.good_reason
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.accepted_unpadded
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.missing_length
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.truncated_payload
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.wrong_selector
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.wrong_kind
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.wrong_order
#check Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.populated_client

#eval IO.println ("SOURCE_ERROR_BYTES=" ++ Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.jsonPackets (Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.messages.map Solidity.Source.errorData))

#eval IO.println ("INTRINSIC_ERROR_BYTES=" ++ Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.jsonPackets (Solidity.Lowering.V08.LiteralFailureBytesReadbackControls.messages.map (fun bs=>Solidity.Source.errorSelector ++ Solidity.AbiEntry.encodeArgs (Solidity.Lowering.V08.LiteralFailureBytesReadback.values bs))))
