import Solidity.Backend.AbiWorld.TypedPacketMaterialize
import Solidity.Backend.AbiWorld.MutatingWritePhysicalControls
namespace Solidity.Backend.AbiWorld.TypedPacketMaterializeControls
open Solidity.Backend
open MemoryOps.Physical
abbrev I := MutatingWritePhysicalControls.bytes
abbrev vals := LibraryResultPacket.values ⟨42,by decide⟩ [0,255]
def packet := AbiEntry.encodeArgs vals
def code := Environment.materialize 0 packet++[.op .REVERT]
def application (frame : Environment.Frame) (tail : List Roadmap.Word) :=
 TypedPacketMaterialize.execute vals (by decide +kernel)
 MutatingWritePhysicalControls.before I MutatingWritePhysicalControls.live
 MutatingWritePhysicalControls.initial frame ⟨0,by decide⟩ ⟨128,by decide⟩ tail [] []
 (by decide +kernel) (by decide +kernel)
 (by intro c h;rcases h with rfl|rfl <;> decide +kernel)

theorem exact_limit (frame : Environment.Frame) :
 Failure.Slice.checkedRun code ⟨⟨0,by decide⟩::⟨128,by decide⟩::List.replicate 1020 ⟨77,by decide⟩,I⟩=
 some (⟨List.replicate 1020 ⟨77,by decide⟩,Environment.writeBytes I 0 packet⟩,some (.revert packet)) := by
 simpa only [List.length_replicate,show 1020+4≤1024 from by decide,if_true] using
 (application frame (List.replicate 1020 ⟨77,by decide⟩)).2.1

theorem one_over_limit (frame : Environment.Frame) :
 Failure.Slice.checkedRun code ⟨⟨0,by decide⟩::⟨128,by decide⟩::List.replicate 1021 ⟨77,by decide⟩,I⟩=none := by
 simpa only [List.length_replicate,show ¬1021+4≤1024 from by decide,if_false] using
 (application frame (List.replicate 1021 ⟨77,by decide⟩)).2.1

theorem empty_baseline : Failure.Slice.checkedRun [.op .REVERT]
 ⟨[⟨0,by decide⟩,⟨0,by decide⟩,⟨77,by decide⟩],I⟩=
 some (⟨[⟨77,by decide⟩],I⟩,some (.revert [])) := by rfl

theorem wrong_head_offset : packet≠Semantics.wordBytes 42++Semantics.wordBytes 32++
 Semantics.wordBytes 2++Semantics.pad32 [0,255] := by decide +kernel

def render (bs : List UInt8) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
#eval IO.println (match Failure.Slice.checkedRun code ⟨[⟨0,by decide⟩,⟨128,by decide⟩,⟨77,by decide⟩],I⟩ with
 | some (_,some (.revert bytes)) => "TYPED_PACKET_REVERT="++render bytes
 | _ => "UNEXPECTED")
/-- info: 'Solidity.Backend.AbiWorld.TypedPacketMaterialize.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TypedPacketMaterialize.execute
/-- info: 'Solidity.Backend.AbiWorld.TypedPacketMaterializeControls.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms application
/-- info: 'Solidity.Backend.AbiWorld.TypedPacketMaterializeControls.exact_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_limit
/-- info: 'Solidity.Backend.AbiWorld.TypedPacketMaterializeControls.one_over_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms one_over_limit
/-- info: 'Solidity.Backend.AbiWorld.TypedPacketMaterializeControls.empty_baseline' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms empty_baseline
/-- info: 'Solidity.Backend.AbiWorld.TypedPacketMaterializeControls.wrong_head_offset' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms wrong_head_offset
end Solidity.Backend.AbiWorld.TypedPacketMaterializeControls
