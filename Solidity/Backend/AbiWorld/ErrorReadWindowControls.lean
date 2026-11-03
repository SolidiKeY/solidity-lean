import Solidity.Backend.AbiWorld.ErrorReadWindow
import Solidity.Semantics.RevertData

namespace Solidity.Backend.AbiWorld.ErrorReadWindowControls
open Semantics Failure ErrorReadWindow

def machine : Slice.Machine :=
  { stack := [⟨11, by decide⟩, ⟨22, by decide⟩], memory := fun _ => 165 }
def messages : List (List UInt8) :=
  [[], [0], [255], [0,255,128], List.replicate 31 0, List.replicate 32 255, List.replicate 33 128]
def suffix : List UInt8 := [222,173,0,255]
def packets : List (List UInt8) :=
  messages.map (fun bs => (encodeError bs).take (68+bs.length) ++ suffix)

local instance (a : Nat) (bs : List UInt8) : Decidable (Fits a bs) :=
  inferInstanceAs (Decidable (a<wordLimit ∧ bs.length<wordLimit ∧ a+bs.length≤wordLimit))

theorem fits_messages : messages.all (fun bs => decide (Fits 8 ((encodeError bs).take (68+bs.length) ++ suffix))) = true := by
  decide

theorem populated (bs : List UInt8) (member : bs ∈ messages) :
    let data := (encodeError bs).take (68+bs.length) ++ suffix
    Slice.checkedRun (emit 8 (.custom data)) machine =
      some ({machine with memory := Slice.putBytes machine.memory 8 data}, some (Roadmap.Outcome.revert data)) ∧
    Slice.getBytes (Slice.putBytes machine.memory 8 data) 8 data.length = data ∧
    decodeError (Slice.getBytes (Slice.putBytes machine.memory 8 data) 8 data.length) = some bs := by
  have fits : Fits 8 ((encodeError bs).take (68+bs.length) ++ suffix) :=
    of_decide_eq_true ((List.all_eq_true.mp fits_messages) bs member)
  simpa only [List.append_nil] using emitted bs suffix 8 [] machine fits (by decide)

theorem older_byte (bs : List UInt8) :
    Slice.putBytes machine.memory 8 ((encodeError bs).take (68+bs.length) ++ suffix) 7 = 165 := by
  exact Slice.putBytes_frame _ _ _ _ (.inl (by decide))

theorem lengths : packets.map List.length = [72,73,73,75,103,104,105] := by decide

theorem dirty_padding :
    decodeError ((encodeError [0,255]).take 70 ++ List.replicate 30 165) = some [0,255] := by decide

theorem dirty_differs :
    (encodeError [0,255]).take 70 ++ List.replicate 30 165 ≠ encodeError [0,255] := by decide

theorem truncated : decodeError ((encodeError [0,255]).take 69) = none := by decide

theorem missing_length : decodeError ((encodeError [0,255]).take 67) = none := by decide

/-- A suffix can supply a missing payload byte; completeness is essential. -/
theorem suffix_fills_missing :
    decodeError ((encodeError [0,255]).take 69 ++ [128]) = some [0,128] := by decide

theorem stale_reason_rejected :
    decodeError ((encodeError [0,255]).take 69 ++ [128]) ≠ some [0,255] := by decide

theorem wrong_selector :
    decodeError (0 :: ((encodeError [0,255]).take 70 ++ suffix).drop 1) = none := by decide

theorem wrong_kind : Semantics.decodePanic ((encodeError [0,255]).take 70 ++ suffix) = none := by decide

theorem full_packet_differs : (encodeError [0,255]).take 70 ++ suffix ≠ encodeError [0,255] := by decide

theorem exact_capacity : Fits (wordLimit-74) ((encodeError [0,255]).take 70 ++ suffix) := by decide

theorem one_past_capacity : ¬ Fits (wordLimit-73) ((encodeError [0,255]).take 70 ++ suffix) := by decide

/-- Only serializes existing observations, not an ABI encoder. -/
def jsonBytes (bs : List UInt8) : String :=
  "[" ++ String.intercalate "," (bs.map (fun b => toString b.toNat)) ++ "]"
def jsonPackets (ps : List (List UInt8)) : String :=
  "[" ++ String.intercalate "," (ps.map jsonBytes) ++ "]"
end Solidity.Backend.AbiWorld.ErrorReadWindowControls

#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.populated
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.fits_messages
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.older_byte
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.dirty_padding
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.suffix_fills_missing
#eval IO.println ("UNPADDED_PACKETS=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets Solidity.Backend.AbiWorld.ErrorReadWindowControls.packets)
#eval IO.println ("READBACK_PACKETS=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets (Solidity.Backend.AbiWorld.ErrorReadWindowControls.packets.map (fun bs => Solidity.Backend.Failure.Slice.getBytes (Solidity.Backend.Failure.Slice.putBytes Solidity.Backend.AbiWorld.ErrorReadWindowControls.machine.memory 8 bs) 8 bs.length)))
#eval IO.println ("DECODED_REASONS=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets (Solidity.Backend.AbiWorld.ErrorReadWindowControls.packets.map (fun bs => (Solidity.Semantics.decodeError bs).getD [])))

#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.lengths
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.dirty_differs
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.truncated
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.missing_length
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.stale_reason_rejected
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.wrong_selector
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.wrong_kind
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.full_packet_differs
#eval IO.println ("DECODE_PRESENT=" ++ "[" ++ String.intercalate "," (Solidity.Backend.AbiWorld.ErrorReadWindowControls.packets.map (fun bs => toString (Solidity.Semantics.decodeError bs).isSome)) ++ "]")

#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.exact_capacity
#print axioms Solidity.Backend.AbiWorld.ErrorReadWindowControls.one_past_capacity
