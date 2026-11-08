import Solidity.Backend.AbiEntry.SelectorMatch

/-! Inhabited raw-prefix matches and a real padded partial-prefix collision.
The latter requires dispatch's short-input guard; numeric match alone is not it. -/
namespace Solidity.Backend.AbiEntry.SelectorMatchControls
open Scalar
private def selector : Vector UInt8 4 := #v[0xde,0xad,0xbe,0xef]
private def partialSelector : Vector UInt8 4 := #v[0x12,0x34,0,0]
private def suffix : Stack := [258,513]
private def frame (bytes : List UInt8) : Source.Fr :=
  {this := ⟨0,by decide⟩,sender := ⟨0,by decide⟩,value := ⟨0,by decide⟩,
   static := false,contract := "",cd := bytes}
private def full : Source.Fr := frame [0xde,0xad,0xbe,0xef,1,2,3,4,0xff]
private def other : Source.Fr := frame [0xde,0xad,0xbe,0xee,1,2,3,4,0xff]
private def partialFrame : Source.Fr := frame [0x12,0x34]

theorem raw_match :
    run (SelectorMatch.code selector) (BitVec.ofNat 256 (Solidity.AbiEntry.load full.cd 0)::suffix)=
      some (1::suffix) := by
  rw [SelectorMatch.raw _ full (by decide) suffix]
  rfl

theorem raw_mismatch :
    run (SelectorMatch.code selector) (BitVec.ofNat 256 (Solidity.AbiEntry.load other.cd 0)::suffix)=
      some (0::suffix) := by
  rw [SelectorMatch.raw _ other (by decide) suffix]
  rfl

theorem low_payload_ignored :
    run (SelectorMatch.code selector) (BitVec.ofNat 256 (0xdeadbeef*2^224)::suffix)=some (1::suffix) ∧
    run (SelectorMatch.code selector) (BitVec.ofNat 256 (0xdeadbeef*2^224+(2^224-1))::suffix)=
      some (1::suffix) := by decide

theorem padded_partial_collision :
    run (SelectorMatch.code partialSelector)
      (BitVec.ofNat 256 (Solidity.AbiEntry.load partialFrame.cd 0)::suffix)=some (1::suffix) ∧
    (partialFrame.cd.take 4==partialSelector.toList)=false := by decide

theorem empty_not_source_match : (([] : List UInt8).take 4==(#v[0,0,0,0] : Vector UInt8 4).toList)=false :=
  SelectorMatch.short_no_match _ [] (by decide)

theorem capacity_refused : stackBound (SelectorMatch.code selector) 1024=false := by decide

theorem inhabited_frame :
    (SelectorMatch.frameCertificate selector (BitVec.ofNat 256 (0xdeadbeef*2^224))).peak=1 ∧
    run (SelectorMatch.frameCertificate selector (BitVec.ofNat 256 (0xdeadbeef*2^224))).code
      (BitVec.ofNat 256 (0xdeadbeef*2^224)::suffix)=some (1::suffix) := ⟨rfl,low_payload_ignored.1⟩

/-- info: 'Solidity.Backend.AbiEntry.SelectorMatchControls.raw_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_match
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatchControls.raw_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_mismatch
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatchControls.low_payload_ignored' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms low_payload_ignored
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatchControls.padded_partial_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_partial_collision
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatchControls.empty_not_source_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_not_source_match
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatchControls.capacity_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_refused
/-- info: 'Solidity.Backend.AbiEntry.SelectorMatchControls.inhabited_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited_frame
end Solidity.Backend.AbiEntry.SelectorMatchControls
