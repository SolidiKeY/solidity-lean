import Solidity.Backend.AbiWorld.PacketPrefix
import Solidity.Backend.AbiWorld.LibraryResultPacket
import Solidity.Backend.AbiWorld.ErrorReadWindowControls

namespace Solidity.Backend.AbiWorld.PacketPrefixControls
open Failure PacketPrefix
open ErrorReadWindowControls (machine jsonBytes)

def payload : List UInt8 := AbiEntry.encodeArgs (LibraryResultPacket.values ⟨300,by decide⟩ [0,255])
local instance (a : Nat) (bs : List UInt8) : Decidable (Fits a bs) :=
  inferInstanceAs (Decidable (a<wordLimit ∧ bs.length<wordLimit ∧ a+bs.length≤wordLimit))
theorem payload_length : payload.length = 128 := by
  rw [payload,LibraryResultPacket.length]
  rfl
theorem fits : Fits 8 payload := by
  simp only [Fits,payload_length]
  decide

theorem boundary_applied (k : Nat) (hk : k ≤ payload.length) :
    Slice.checkedRun ((emit 8 (.returned payload)).take (3*k)) machine =
      some ({machine with memory := Slice.putBytes machine.memory 8 (payload.take k)},none) :=
  boundary 8 (.returned payload) k hk machine fits (by decide)

theorem byte_applied (k : Nat) (hk : k < payload.length) :
    Slice.checkedRun ((emit 8 (.returned payload)).take (3*k+1)) machine =
      some ({machine with memory := Slice.putBytes machine.memory 8 (payload.take k), stack :=
        ⟨(payload[k]).toNat,byte_lt_word _⟩ :: machine.stack},none) :=
  byte_push 8 (.returned payload) k hk machine fits (by decide)

theorem address_applied (k : Nat) (hk : k < payload.length) :
    let ha : 8+k < wordLimit := by have h := fits.2.2; omega
    Slice.checkedRun ((emit 8 (.returned payload)).take (3*k+2)) machine =
      some ({machine with memory := Slice.putBytes machine.memory 8 (payload.take k), stack :=
        ⟨8+k,ha⟩ :: ⟨(payload[k]).toNat,byte_lt_word _⟩ :: machine.stack},none) :=
  byte_offset_push 8 (.returned payload) k hk machine fits (by decide)

theorem before_terminal :
    (Slice.checkedRun ((emit 8 (.returned payload)).take (3*payload.length+2)) machine).map Prod.snd = some none := by
  simpa only [Input.bytes,Option.map_some] using congrArg (fun r => r.map Prod.snd)
    (offset_push 8 (.returned payload) machine fits (by decide))

theorem not_early_success :
    (Slice.checkedRun ((emit 8 (.returned payload)).take (3*payload.length+2)) machine).map Prod.snd ≠
      some (some (.success payload)) := by rw [before_terminal]; decide

theorem terminal_modes :
    (Slice.checkedRun ((emit 8 (.returned payload)).take (3*payload.length+3)) machine).map Prod.snd =
      some (some (.success payload)) ∧
    (Slice.checkedRun ((emit 8 (.custom payload)).take (3*payload.length+3)) machine).map Prod.snd =
      some (some (.revert payload)) := by
  constructor
  · simpa only [Input.bytes,Input.observation,Option.map_some] using congrArg (fun r => r.map Prod.snd)
      (complete 8 (.returned payload) machine fits (by decide))
  · simpa only [Input.bytes,Input.observation,Option.map_some] using congrArg (fun r => r.map Prod.snd)
      (complete 8 (.custom payload) machine fits (by decide))

theorem pending_byte_unchanged :
    (Slice.checkedRun ((emit 8 (.returned payload)).take 2) machine).map
      (fun s => s.1.memory 8) = some 165 := by
  rw [show 2=3*0+2 by decide,byte_offset_push 8 (.returned payload) 0 (by change 0<payload.length; rw [payload_length]; decide) machine fits (by decide)]
  rfl

theorem byte_zero_written :
    (Slice.checkedRun ((emit 8 (.returned payload)).take 3) machine).map
      (fun s => s.1.memory 8) = some 0 := by
  have first : payload.take 1 = [0] := by
    rw [payload,LibraryResultPacket.encoded_values]
    rfl
  have h := boundary 8 (.returned payload) 1 (by change 1≤payload.length; rw [payload_length]; decide) machine fits (by decide)
  have observed := congrArg (fun r => r.map (fun s => s.1.memory 8)) h
  simpa only [Input.bytes,first,Slice.putBytes,Slice.putByte,Option.map_some,ite_true] using observed

def crowded : Slice.Machine := {machine with stack := List.replicate 1023 ⟨11,by decide⟩}
theorem crowded_refused : Slice.checkedRun ((emit 8 .empty).take 2) crowded = none := by
  change (if Slice.stackSafe [pushNat 0,pushNat 8] crowded then _ else none) = none
  have rejected : Slice.stackSafe [pushNat 0,pushNat 8] crowded = false := by
    rw [stackSafe_pushNat 0 (by decide),stackSafe_pushNat 8 (by decide)]
    simp only [Slice.stackSafe,List.length_cons,crowded,List.length_replicate]
    rfl
  rw [rejected]
  rfl

theorem unsupported_tail_unreachable :
    (Slice.checkedRun ((emit 8 (.returned payload) ++ ([.op .ADD] : Program)).take (3*payload.length+4)) machine).map Prod.snd =
      some (some (.success payload)) := by
  simpa only [Input.bytes,Input.observation,Option.map_some] using congrArg (fun r => r.map Prod.snd)
    (after_terminal 8 (.returned payload) ([.op .ADD] : Program) (3*payload.length+4) (by simp only [Input.bytes,payload_length]; decide) machine fits (by decide))

def cuts : List Nat := [0,1,2,3,90,91,92,93,94,95,96,97,98,189,190,191,192,285,286,287,288,289,290,291,292,293,381,382,383,384,385,386,387]

def natList (ns : List Nat) : String := "[" ++ String.intercalate "," (ns.map toString) ++ "]"
def rowFrom (machine : Slice.Machine) (i : Input) (cut : Nat) : String :=
  let rowHead := "{\"cut\":" ++ toString cut
  match Slice.checkedRun ((emit 8 i).take cut) machine with
  | none => rowHead ++ ",\"fault\":true}"
  | some (st,out) =>
    rowHead ++ ",\"fault\":false,\"stack\":" ++ natList (st.stack.map Fin.val) ++
      ",\"memory\":" ++ jsonBytes (Slice.getBytes st.memory 8 i.bytes.length) ++
      ",\"older\":" ++ toString (st.memory 7).toNat ++
      ",\"after\":" ++ toString (st.memory (8+i.bytes.length)).toNat ++
      ",\"outcome\":" ++ (match out with
        | none => "\"pending\""
        | some (.success bs) => "{\"return\":" ++ jsonBytes bs ++ "}"
        | some (.revert bs) => "{\"revert\":" ++ jsonBytes bs ++ "}") ++ "}"

def row (i : Input) (cut : Nat) : String := rowFrom machine i cut

def rows (i : Input) (cs : List Nat) : String := "[" ++ String.intercalate "," (cs.map (row i)) ++ "]"
end Solidity.Backend.AbiWorld.PacketPrefixControls
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.fits
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.payload_length
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.boundary_applied
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.byte_applied
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.address_applied
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.before_terminal
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.not_early_success
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.terminal_modes
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.pending_byte_unchanged
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.byte_zero_written
#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.crowded_refused
#eval IO.println ("RETURN_PREFIXES=" ++ Solidity.Backend.AbiWorld.PacketPrefixControls.rows (.returned Solidity.Backend.AbiWorld.PacketPrefixControls.payload) Solidity.Backend.AbiWorld.PacketPrefixControls.cuts)
#eval IO.println ("REVERT_PREFIXES=" ++ Solidity.Backend.AbiWorld.PacketPrefixControls.rows (.custom Solidity.Backend.AbiWorld.PacketPrefixControls.payload) [384,385,386,387])
#eval IO.println ("EMPTY_PREFIXES=" ++ Solidity.Backend.AbiWorld.PacketPrefixControls.rows .empty [0,1,2,3])
#eval IO.println ("PANIC_PREFIXES=" ++ Solidity.Backend.AbiWorld.PacketPrefixControls.rows (.panic ⟨300,by decide⟩) [93,94,95,96,97,98,99,108,109,110,111])

#eval IO.println ("ERROR_PREFIXES=" ++ Solidity.Backend.AbiWorld.PacketPrefixControls.rows (.reason [0,255]) [204,205,206,207,300,301,302,303])
#eval IO.println ("CROWDED_PREFIXES=" ++ "[" ++ String.intercalate "," ([0,1,2,3].map (Solidity.Backend.AbiWorld.PacketPrefixControls.rowFrom Solidity.Backend.AbiWorld.PacketPrefixControls.crowded .empty)) ++ "]")

#print axioms Solidity.Backend.AbiWorld.PacketPrefixControls.unsupported_tail_unreachable
