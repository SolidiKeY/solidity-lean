import Solidity.Backend.AbiWorld.ErrorOffsetWindow
import Solidity.Backend.AbiWorld.ErrorReadWindowControls

namespace Solidity.Backend.AbiWorld.ErrorOffsetWindowControls
open Semantics Failure ErrorOffsetWindow
open ErrorReadWindowControls (machine messages suffix jsonPackets)

def gaps : List (List UInt8) := [[],[165],[0,255,128],List.replicate 31 170,List.replicate 32 187,List.replicate 33 204]
/-- Test observations of the existing decoder inputs; no alternative ABI codec. -/
def data (gap bs : List UInt8) : List UInt8 :=
  errorSelector ++ wordBytes (32+gap.length) ++ gap ++ wordBytes bs.length ++ bs ++ suffix

def packets : List (List UInt8) := gaps.flatMap (fun gap => messages.map (data gap))

local instance (a : Nat) (bs : List UInt8) : Decidable (Fits a bs) :=
  inferInstanceAs (Decidable (a<wordLimit ∧ bs.length<wordLimit ∧ a+bs.length≤wordLimit))

theorem fits_all : gaps.all (fun gap => messages.all (fun bs => decide (Fits 8 (data gap bs)))) = true := by decide

theorem populated (gap bs : List UInt8) (hg : gap ∈ gaps) (hb : bs ∈ messages) :
    Slice.checkedRun (emit 8 (.custom (data gap bs))) machine =
      some ({machine with memory := Slice.putBytes machine.memory 8 (data gap bs)},some (Roadmap.Outcome.revert (data gap bs))) ∧
    Slice.getBytes (Slice.putBytes machine.memory 8 (data gap bs)) 8 (data gap bs).length = data gap bs ∧
    decodeError (Slice.getBytes (Slice.putBytes machine.memory 8 (data gap bs)) 8 (data gap bs).length) = some bs := by
  have hf : Fits 8 (data gap bs) :=
    of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp fits_all) gap hg)) bs hb)
  simpa only [List.append_nil,data] using emitted gap bs suffix 8 [] machine hf (by decide)

theorem offsets : gaps.map (fun gap => bytesNat ((data gap [17,34]).drop 4 |>.take 32)) = [32,33,35,63,64,65] := by decide

theorem gap_content_ignored : decodeError (data [165] [17,34]) = decodeError (data [90] [17,34]) := by decide

theorem gap_bytes_retained : data [165] [17,34] ≠ data [90] [17,34] := by decide

theorem wrong_offset :
    decodeError (errorSelector ++ wordBytes 34 ++ [165] ++ wordBytes 2 ++ [17,34] ++ suffix) = none := by decide

theorem truncated_head : decodeError (errorSelector ++ (wordBytes 33).take 31) = none := by decide

theorem missing_length : decodeError (errorSelector ++ wordBytes 33 ++ [165] ++ (wordBytes 2).take 31) = none := by decide

theorem truncated_payload : decodeError (errorSelector ++ wordBytes 33 ++ [165] ++ wordBytes 2 ++ [17]) = none := by decide

theorem zero_alias : decodeError (errorSelector ++ wordBytes 0 ++ [17,34]) = some [] := by decide

theorem zero_not_reason : decodeError (errorSelector ++ wordBytes 0 ++ [17,34]) ≠ some [17,34] := by decide

theorem reordered_payload : decodeError (data [165] [17,34]) ≠ some [34,17] := by decide

theorem older_byte (gap bs : List UInt8) : Slice.putBytes machine.memory 8 (data gap bs) 7 = 165 := by
  exact Slice.putBytes_frame _ _ _ _ (.inl (by decide))

theorem exact_capacity : Fits (wordLimit-75) (data [165] [17,34]) := by decide

theorem one_past_capacity : ¬ Fits (wordLimit-74) (data [165] [17,34]) := by decide
end Solidity.Backend.AbiWorld.ErrorOffsetWindowControls
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.fits_all
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.populated
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.offsets
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.gap_content_ignored
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.gap_bytes_retained
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.wrong_offset
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.truncated_head
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.missing_length
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.truncated_payload
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.zero_alias
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.zero_not_reason
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.reordered_payload
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.older_byte
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.exact_capacity
#print axioms Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.one_past_capacity
#eval IO.println ("OFFSET_PACKETS=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.packets)
#eval IO.println ("OFFSET_READBACK=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets (Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.packets.map (fun bs => Solidity.Backend.Failure.Slice.getBytes (Solidity.Backend.Failure.Slice.putBytes Solidity.Backend.AbiWorld.ErrorReadWindowControls.machine.memory 8 bs) 8 bs.length)))
#eval IO.println ("OFFSET_REASONS=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets (Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.packets.map (fun bs => (Solidity.Semantics.decodeError bs).getD [])))
#eval IO.println ("OFFSET_PRESENT=" ++ "[" ++ String.intercalate "," (Solidity.Backend.AbiWorld.ErrorOffsetWindowControls.packets.map (fun bs => toString (Solidity.Semantics.decodeError bs).isSome)) ++ "]")
