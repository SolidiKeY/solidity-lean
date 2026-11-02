import Solidity.Backend.AbiWorld.SiblingReadback
import tests.«v13-abi-world».RecursiveFailureControls
namespace Solidity.Backend.AbiWorld.SiblingControls
open AbiEntry RecursiveLayout RecursiveEntry SiblingReadback

def ps : List Param := [{shape := RecursiveControls.Row,loc := .memory},{shape := .bytes,loc := .calldata}]
def vs : Vals (ps.map Param.shape) := .cons (RecursiveControls.row [0,255])
  (.cons (.bytes ((List.range 31).map UInt8.ofNat)) .nil)
def qs : List Param := [{shape := .array .bytes,loc := .memory}]
def later (bs : List (List UInt8)) : Vals (qs.map Param.shape) :=
  .cons (.array (ByteSequenceControls.sequence bs)) .nil
def lo := later []
def hi := later [[],(List.range 33).map UInt8.ofNat]
def sel : List UInt8 := [0,1,0,255]
def post : List UInt8 := List.replicate 32 0 ++ [42,0]
def sample (ws : Vals (qs.map Param.shape)) : Input :=
  input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) sel post 128

theorem measurements : headsOf ps = 64 ∧ headsOf qs = 32 ∧ memberAllocation vs = 288 ∧
    LocationPeak.peak ps vs = 288 ∧ spent ps vs = 224 ∧ parameterNeed vs = 10 ∧ memberNeed vs = 11 := by decide +kernel

theorem row_length : (AbiEntry.Val.enc (RecursiveControls.row [0,255])).length = 192 := by
  change (AbiEntry.assemble (Vals.parts (.cons (RecursiveControls.w 300 (by decide))
    (.cons (.fixed RecursiveControls.pair) (.cons (.bytes [0,255]) .nil))))).length = 192
  rw [assemble_length]
  have fixed_length := static_length (.fixed RecursiveControls.pair) (by decide)
  simp only [Vals.parts,heads,List.foldr_cons,List.foldr_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Shape.dynamic,Bool.false_eq_true,ite_false,ite_true,
    show (AbiEntry.Val.enc (RecursiveControls.w 300 (by decide))).length = 32 by exact MixedPacket.word_length _,
    fixed_length]
  decide +kernel

theorem prefix_tail_length (off : Nat) : (AbiEntry.assemble.go (Vals.parts vs) off).2.length = 256 := by
  rw [tail_length]
  simp only [vs,Vals.parts,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Shape.dynamic,ite_true,
    row_length]
  decide +kernel

theorem later_tail_length (bs : List (List UInt8)) (off : Nat) :
    (AbiEntry.assemble.go (Vals.parts (later bs)) off).2.length =
      (AbiEntry.Val.enc (.array (ByteSequenceControls.sequence bs))).length := by
  rw [tail_length]
  simp only [later,Vals.parts,Shape.dynamic,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

theorem size_formula (bs : List (List UInt8)) :
    (sample (later bs)).size = 390 + (AbiEntry.Val.enc (.array (ByteSequenceControls.sequence bs))).length := by
  change (input (ps ++ qs) (BodyComposition.appendValues ps qs vs (later bs)) sel post 128).size = _
  rw [canonical_size,prefix_tail_length,later_tail_length,measurements.1,measurements.2.1]
  simp only [sel,post,List.length_append,List.length_cons,List.length_nil,List.length_replicate]
  omega

theorem sizes : (sample lo).size = 422 ∧ (sample hi).size = 614 := by
  constructor <;> simp only [lo,hi,size_formula,ByteSequenceReadback.array_length,ByteSequenceControls.tail_sequence,
    List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  all_goals decide +kernel

theorem typed_pair :
    (enter (sample lo) 11 ps 0 17).map (fun r => (bodyValues (sample lo) 11 ps r.1 0,r.2)) = .ok (.ok vs,241) ∧
    (enter (sample hi) 11 ps 0 17).map (fun r => (bodyValues (sample hi) 11 ps r.1 0,r.2)) = .ok (.ok vs,241) := by
  apply noninterference ps qs vs lo hi sel post 128 17 11
  · decide +kernel
  · decide +kernel
  · rw [show (input (ps ++ qs) (BodyComposition.appendValues ps qs vs lo) sel post 128).size = 422 from sizes.1]; decide +kernel
  · rw [show (input (ps ++ qs) (BodyComposition.appendValues ps qs vs hi) sel post 128).size = 614 from sizes.2]; decide +kernel
  · decide +kernel
  · decide +kernel

theorem prefix_entries : (∃ es, entry (sample lo) 11 ps = .ok es ∧ bodyValues (sample lo) 11 ps es 0 = .ok vs) ∧
    (∃ es, entry (sample hi) 11 ps = .ok es ∧ bodyValues (sample hi) 11 ps es 0 = .ok vs) := by
  constructor
  · apply prefix_entry ps qs vs lo sel post 128 11
    · decide +kernel
    · decide +kernel
    · rw [show (input (ps ++ qs) (BodyComposition.appendValues ps qs vs lo) sel post 128).size = 422 from sizes.1]; decide +kernel
    · decide +kernel
    · decide +kernel
  · apply prefix_entry ps qs vs hi sel post 128 11
    · decide +kernel
    · decide +kernel
    · rw [show (input (ps ++ qs) (BodyComposition.appendValues ps qs vs hi) sel post 128).size = 614 from sizes.2]; decide +kernel
    · decide +kernel
    · decide +kernel

theorem decoder_pair : mmembers (sample lo) 11 (ps.map Param.shape) 4 0 17 = .ok (vs,305) ∧
    mmembers (sample hi) 11 (ps.map Param.shape) 4 0 17 = .ok (vs,305) := by
  constructor
  · apply decoder_canonical ps qs vs lo sel post 128 17 11
    · decide +kernel
    · decide +kernel
    · rw [show (input (ps ++ qs) (BodyComposition.appendValues ps qs vs lo) sel post 128).size = 422 from sizes.1]; decide +kernel
    · decide +kernel
    · decide +kernel
  · apply decoder_canonical ps qs vs hi sel post 128 17 11
    · decide +kernel
    · decide +kernel
    · rw [show (input (ps ++ qs) (BodyComposition.appendValues ps qs vs hi) sel post 128).size = 614 from sizes.2]; decide +kernel
    · decide +kernel
    · decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.parts_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.parts_append
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.encoded_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.encoded_split
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.canonical_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.canonical_size
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.prefix_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.prefix_bytes
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.window_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.window_size
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.window
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.members_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.members_window
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.canonical
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.decoder_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.decoder_canonical
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.prefix_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.prefix_entry
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.byte_noninterference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.byte_noninterference
/-- info: 'Solidity.Backend.AbiWorld.SiblingReadback.noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingReadback.noninterference
/-- info: 'Solidity.Backend.AbiWorld.SiblingControls.measurements' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingControls.measurements
/-- info: 'Solidity.Backend.AbiWorld.SiblingControls.row_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingControls.row_length
/-- info: 'Solidity.Backend.AbiWorld.SiblingControls.prefix_tail_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingControls.prefix_tail_length
/-- info: 'Solidity.Backend.AbiWorld.SiblingControls.later_tail_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingControls.later_tail_length
/-- info: 'Solidity.Backend.AbiWorld.SiblingControls.size_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingControls.size_formula
/-- info: 'Solidity.Backend.AbiWorld.SiblingControls.sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingControls.sizes
/-- info: 'Solidity.Backend.AbiWorld.SiblingControls.typed_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingControls.typed_pair
/-- info: 'Solidity.Backend.AbiWorld.SiblingControls.prefix_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingControls.prefix_entries
/-- info: 'Solidity.Backend.AbiWorld.SiblingControls.decoder_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingControls.decoder_pair
end Solidity.Backend.AbiWorld.SiblingControls
