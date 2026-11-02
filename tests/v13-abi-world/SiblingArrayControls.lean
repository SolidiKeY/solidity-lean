import tests.«v13-abi-world».SiblingFixtures
namespace Solidity.Backend.AbiWorld.SiblingArrayControls
open AbiEntry RecursiveLayout RecursiveEntry SiblingReadback

def ps : List Param := [{shape := .array RecursiveControls.Row,loc := .memory}]
def vs : Vals (ps.map Param.shape) :=
  .cons (.array (.cons (RecursiveControls.row []) .nil)) .nil
def sample (ws : Vals (SiblingControls.qs.map Param.shape)) : Input :=
  input (ps ++ SiblingControls.qs) (BodyComposition.appendValues ps SiblingControls.qs vs ws)
    SiblingControls.sel SiblingControls.post 128

theorem measurements : headsOf ps = 32 ∧ memberAllocation vs = 256 ∧ LocationPeak.peak ps vs = 256 ∧
    spent ps vs = 256 ∧ parameterNeed vs = 13 ∧ memberNeed vs = 14 ∧
    (AbiEntry.Val.enc (.array (.cons (RecursiveControls.row []) .nil))).length = 224 := by
  decide +kernel

theorem tail_extent (off : Nat) : (AbiEntry.assemble.go (Vals.parts vs) off).2.length = 224 := by
  rw [tail_length]
  simp only [vs,Vals.parts,Shape.dynamic,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  exact measurements.2.2.2.2.2.2

theorem size_formula (bs : List (List UInt8)) :
    (sample (SiblingControls.later bs)).size = 326 +
      (AbiEntry.Val.enc (.array (ByteSequenceControls.sequence bs))).length := by
  change (input (ps ++ SiblingControls.qs) (BodyComposition.appendValues ps SiblingControls.qs vs (SiblingControls.later bs))
    SiblingControls.sel SiblingControls.post 128).size = _
  rw [canonical_size,tail_extent,SiblingControls.later_tail_length,measurements.1,SiblingControls.measurements.2.1]
  simp only [SiblingControls.sel,SiblingControls.post,List.length_append,List.length_cons,List.length_nil,List.length_replicate]
  omega

theorem sizes : (sample SiblingControls.lo).size = 358 ∧ (sample SiblingControls.hi).size = 550 := by
  constructor <;> simp only [SiblingControls.lo,SiblingControls.hi,size_formula,ByteSequenceReadback.array_length,
    ByteSequenceControls.tail_sequence,List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  all_goals decide +kernel

theorem typed_pair :
    (enter (sample SiblingControls.lo) 14 ps 0 17).map (fun r => (bodyValues (sample SiblingControls.lo) 14 ps r.1 0,r.2)) = .ok (.ok vs,273) ∧
    (enter (sample SiblingControls.hi) 14 ps 0 17).map (fun r => (bodyValues (sample SiblingControls.hi) 14 ps r.1 0,r.2)) = .ok (.ok vs,273) := by
  apply noninterference ps SiblingControls.qs vs SiblingControls.lo SiblingControls.hi SiblingControls.sel SiblingControls.post 128 17 14
  · decide +kernel
  · decide +kernel
  · rw [show (input (ps ++ SiblingControls.qs) (BodyComposition.appendValues ps SiblingControls.qs vs SiblingControls.lo) SiblingControls.sel SiblingControls.post 128).size = 358 from sizes.1]; decide +kernel
  · rw [show (input (ps ++ SiblingControls.qs) (BodyComposition.appendValues ps SiblingControls.qs vs SiblingControls.hi) SiblingControls.sel SiblingControls.post 128).size = 550 from sizes.2]; decide +kernel
  · decide +kernel
  · decide +kernel

theorem decoder_pair : mmembers (sample SiblingControls.lo) 14 (ps.map Param.shape) 4 0 17 = .ok (vs,273) ∧
    mmembers (sample SiblingControls.hi) 14 (ps.map Param.shape) 4 0 17 = .ok (vs,273) := by
  constructor
  · apply decoder_canonical ps SiblingControls.qs vs SiblingControls.lo SiblingControls.sel SiblingControls.post 128 17 14
    · decide +kernel
    · decide +kernel
    · rw [show (input (ps ++ SiblingControls.qs) (BodyComposition.appendValues ps SiblingControls.qs vs SiblingControls.lo) SiblingControls.sel SiblingControls.post 128).size = 358 from sizes.1]; decide +kernel
    · decide +kernel
    · decide +kernel
  · apply decoder_canonical ps SiblingControls.qs vs SiblingControls.hi SiblingControls.sel SiblingControls.post 128 17 14
    · decide +kernel
    · decide +kernel
    · rw [show (input (ps ++ SiblingControls.qs) (BodyComposition.appendValues ps SiblingControls.qs vs SiblingControls.hi) SiblingControls.sel SiblingControls.post 128).size = 550 from sizes.2]; decide +kernel
    · decide +kernel
    · decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.SiblingArrayControls.measurements' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingArrayControls.measurements
/-- info: 'Solidity.Backend.AbiWorld.SiblingArrayControls.tail_extent' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingArrayControls.tail_extent
/-- info: 'Solidity.Backend.AbiWorld.SiblingArrayControls.size_formula' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingArrayControls.size_formula
/-- info: 'Solidity.Backend.AbiWorld.SiblingArrayControls.sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingArrayControls.sizes
/-- info: 'Solidity.Backend.AbiWorld.SiblingArrayControls.typed_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingArrayControls.typed_pair
/-- info: 'Solidity.Backend.AbiWorld.SiblingArrayControls.decoder_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.SiblingArrayControls.decoder_pair
end Solidity.Backend.AbiWorld.SiblingArrayControls
