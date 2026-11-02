import Solidity.Backend.AbiWorld.LocationPeak
import tests.«v13-abi-world».RecursiveFixtures
namespace Solidity.Backend.AbiWorld.LocationPeakControls
open AbiEntry RecursiveLayout RecursiveEntry

def large : List UInt8 := (List.range 33).map UInt8.ofNat
def sel : List UInt8 := [3,1,4,1]
def post : List UInt8 := List.replicate 32 0 ++ [255]
def repeats : List Param := [{shape := .bytes,loc := .calldata},{shape := .bytes,loc := .calldata}]
def repeatVals : Vals (repeats.map Param.shape) := .cons (.bytes large) (.cons (.bytes large) .nil)
def mixed : List Param := [{shape := .bytes,loc := .calldata},{shape := .bytes,loc := .memory},
  {shape := .bytes,loc := .value},{shape := .word (.uint 256),loc := .value}]
def mixedVals : Vals (mixed.map Param.shape) := .cons (.bytes large) (.cons (.bytes [])
  (.cons (.bytes [0,255]) (.cons (.word UniformWordControls.big) .nil)))

def repeated : Input := input repeats repeatVals sel post (lim-96)
def mixture : Input := input mixed mixedVals sel post (lim-96)
def repeatOver : Input := {repeated with free := repeated.free+1}
def mixedOver : Input := {mixture with free := mixture.free+1}

theorem costs : LocationPeak.peak repeats repeatVals = 96 ∧ spent repeats repeatVals = 0 ∧
    memberAllocation repeatVals = 192 ∧ LocationPeak.peak mixed mixedVals = 96 ∧
    spent mixed mixedVals = 96 ∧ memberAllocation mixedVals = 192 := by decide +kernel

theorem repeat_typed : ∃ es,
    enter repeated 2 repeats 0 0 = .ok (es,0) ∧ entry repeated 2 repeats = .ok es ∧
    bodyValues repeated 2 repeats es 0 = .ok repeatVals ∧ verdict repeated 2 repeats = .run repeatVals ∧
    4 + headsOf repeats ≤ lim := by
  apply LocationPeak.roundtrip repeats repeatVals sel post (lim-96) 2
  all_goals decide +kernel

theorem mixed_typed : ∃ es,
    enter mixture 2 mixed 0 0 = .ok (es,96) ∧ entry mixture 2 mixed = .ok es ∧
    bodyValues mixture 2 mixed es 0 = .ok mixedVals ∧ verdict mixture 2 mixed = .run mixedVals ∧
    4 + headsOf mixed ≤ lim := by
  apply LocationPeak.roundtrip mixed mixedVals sel post (lim-96) 2
  all_goals decide +kernel

theorem new_not_old : repeated.free + LocationPeak.peak repeats repeatVals ≤ lim ∧
    ¬ repeated.free + memberAllocation repeatVals ≤ lim ∧
    mixture.free + LocationPeak.peak mixed mixedVals ≤ lim ∧
    ¬ mixture.free + memberAllocation mixedVals ≤ lim := by decide +kernel

theorem true_failures : DynamicListControls.err (eager repeatOver 2 .bytes 0) = 2 ∧
    (entry repeatOver 2 repeats).toOption.isSome = true ∧
    DynamicListControls.err (entry mixedOver 2 mixed) = 2 ∧
    EntryTransport.bodyObservation repeatOver 2 repeats AbiEntry.encodeArgs = none := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

def switched : List Param := [{shape := .bytes,loc := .memory},{shape := .bytes,loc := .calldata}]
def switchedVals : Vals (switched.map Param.shape) := .cons (.bytes large) (.cons (.bytes large) .nil)
def switchedI : Input := input switched switchedVals sel post (lim-96)
/-- Sufficient is not necessary: order raises this recurrence but the actual
body resets eager allocation to zero. No outside-bound refusal is inferred. -/
theorem nonminimal : LocationPeak.peak switched switchedVals = 192 ∧
    NestedByteControls.cursor switchedI 2 switched = some 96 ∧
    (verdict switchedI 2 switched).kind = "run" := by decide +kernel

def shifted : Input := {mixture with free := lim-113}
theorem shifted_cursor : NestedByteControls.cursor shifted 2 mixed 17 = some 113 ∧
    NestedByteControls.cursor repeated 2 repeats = some 0 ∧
    NestedByteControls.cursor mixture 2 mixed ≠ some 192 := by decide +kernel

open RecursiveControls in
theorem nested_typed : ∃ es,
    enter (RecursiveEntry.input (ps .calldata) (vals .calldata) RecursiveControls.sel RecursiveControls.post (lim-544))
      14 (ps .calldata) 0 0 = .ok (es,192) ∧
    entry (RecursiveEntry.input (ps .calldata) (vals .calldata) RecursiveControls.sel RecursiveControls.post (lim-544))
      14 (ps .calldata) = .ok es ∧
    bodyValues (RecursiveEntry.input (ps .calldata) (vals .calldata) RecursiveControls.sel RecursiveControls.post (lim-544))
      14 (ps .calldata) es 0 = .ok (vals .calldata) ∧
    verdict (RecursiveEntry.input (ps .calldata) (vals .calldata) RecursiveControls.sel RecursiveControls.post (lim-544))
      14 (ps .calldata) = .run (vals .calldata) ∧ 4 + headsOf (ps .calldata) ≤ lim := by
  apply LocationPeak.roundtrip (ps .calldata) (vals .calldata) RecursiveControls.sel RecursiveControls.post (lim-544) 14
  · decide +kernel
  · decide +kernel
  ·
      simp only [RecursiveEntry.input,Input.size,List.length_append,encodeArgs,vals,ps,rows,row,pair,w,
        Val.enc,Vals.parts,Seq.parts,assemble_length,heads,List.foldr_cons,List.foldr_nil,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Shape.dynamic,
        ite_true,ite_false,Bool.false_eq_true,
        MixedPacket.word_length,List.length_nil,List.length_map,List.length_range,
        RecursiveControls.sel,RecursiveControls.post,List.length_cons,List.length_replicate]
      <;> decide +kernel
  · decide +kernel
  · decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.LocationPeak.peak_le_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeak.peak_le_sum
/-- info: 'Solidity.Backend.AbiWorld.LocationPeak.spent_le_peak' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeak.spent_le_peak
/-- info: 'Solidity.Backend.AbiWorld.LocationPeak.room_of_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeak.room_of_sum
/-- info: 'Solidity.Backend.AbiWorld.LocationPeak.calldata_cons' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeak.calldata_cons
/-- info: 'Solidity.Backend.AbiWorld.LocationPeak.window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeak.window
/-- info: 'Solidity.Backend.AbiWorld.LocationPeak.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeak.roundtrip
/-- info: 'Solidity.Backend.AbiWorld.LocationPeakControls.costs' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeakControls.costs
/-- info: 'Solidity.Backend.AbiWorld.LocationPeakControls.repeat_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeakControls.repeat_typed
/-- info: 'Solidity.Backend.AbiWorld.LocationPeakControls.mixed_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeakControls.mixed_typed
/-- info: 'Solidity.Backend.AbiWorld.LocationPeakControls.new_not_old' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeakControls.new_not_old
/-- info: 'Solidity.Backend.AbiWorld.LocationPeakControls.true_failures' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeakControls.true_failures
/-- info: 'Solidity.Backend.AbiWorld.LocationPeakControls.nonminimal' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeakControls.nonminimal
/-- info: 'Solidity.Backend.AbiWorld.LocationPeakControls.shifted_cursor' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeakControls.shifted_cursor
/-- info: 'Solidity.Backend.AbiWorld.LocationPeakControls.nested_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.AbiWorld.LocationPeakControls.nested_typed
end Solidity.Backend.AbiWorld.LocationPeakControls
