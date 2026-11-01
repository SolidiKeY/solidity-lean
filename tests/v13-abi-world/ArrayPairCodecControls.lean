import Solidity.Backend.AbiWorld.ArrayPairPacket
import tests.«v13-abi-world».MixedCodecControls

/-! Pure codec controls: these values are not source admission or compiled
execution witnesses. Complete packets are proved against real encodeArgs. -/
namespace Solidity.Backend.AbiWorld.ArrayPairControls
open Evm Evm.Memory

def firstWords : List PrimTy.uint.Denote := [indexValue (wmod 12),indexValue (wmod 11)]
def lastWords (same : Bool) : List PrimTy.uint.Denote :=
  if same then firstWords else [indexValue (wmod 23),indexValue (wmod 29)]
def packet (same : Bool) : List UInt8 :=
  AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 160 ++
  AbiEntry.wordBytes 2 ++ AbiEntry.wordBytes 12 ++ AbiEntry.wordBytes 11 ++
  AbiEntry.wordBytes 2 ++ AbiEntry.wordBytes (if same then 12 else 23) ++
  AbiEntry.wordBytes (if same then 11 else 29)

theorem encoded (same : Bool) :
    AbiEntry.encodeArgs (ArrayPairPacket.values firstWords (lastWords same)) = packet same := by
  rw [ArrayPairPacket.encoded_words]
  cases same <;> decide +kernel

theorem offsets_and_order (same : Bool) :
    (packet same).length = 256 ∧ ArrayPairPacket.secondOffset firstWords = 160 ∧
    ArrayPairPacket.secondOffset firstWords < AbiEntry.W ∧
    AbiEntry.load (packet same) 0 = 64 ∧ AbiEntry.load (packet same) 32 = 160 ∧
    ((packet same).drop 32).take 32 ≠ AbiEntry.wordBytes 64 ∧
    ((packet same).drop 32).take 32 ≠ AbiEntry.wordBytes 96 ∧
    ((packet same).drop 64).take 96 =
      AbiEntry.wordBytes 2 ++ AbiEntry.wordBytes 12 ++ AbiEntry.wordBytes 11 := by
  cases same <;> decide +kernel

/-- Changing ONLY the second codec value changes neither offsets nor first tail.
This is not a heap-write frame for aliased objects. -/
theorem fixed_prefix : (packet true).take 160 = (packet false).take 160 := by
  have first := ArrayPairPacket.prefix_noninterference firstWords (lastWords true) (lastWords false)
  rw [encoded,encoded] at first
  have off : ArrayPairPacket.secondOffset firstWords = 160 := (offsets_and_order true).2.1
  rw [off] at first
  exact first

def bothEmpty := AbiEntry.encodeArgs (ArrayPairPacket.values [] [])
def emptyFirst := AbiEntry.encodeArgs (ArrayPairPacket.values [] MixedPacketControls.edgeWords)
def emptyLast := AbiEntry.encodeArgs (ArrayPairPacket.values MixedPacketControls.edgeWords [])
def fullWords := AbiEntry.encodeArgs
  (ArrayPairPacket.values MixedPacketControls.edgeWords [MixedPacketControls.edgeScalar])

theorem boundary_words : fullWords =
    AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 160 ++ AbiEntry.wordBytes 2 ++
    AbiEntry.wordBytes 300 ++ List.replicate 32 255 ++ AbiEntry.wordBytes 1 ++ List.replicate 32 255 := by
  rw [fullWords,ArrayPairPacket.encoded_words]
  simp only [MixedPacketControls.edgeWords,List.length_cons,List.length_nil,
    List.flatMap_cons,List.flatMap_nil,indexValue,wmod_of_lt (by decide +kernel : 300 < W),
    Int.toNat_natCast,MixedPacketControls.max_value,MixedPacketControls.max_bytes,
    List.append_nil,List.append_assoc]

theorem empties :
    bothEmpty = AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 96 ++ AbiEntry.wordBytes 0 ++ AbiEntry.wordBytes 0 ∧
    emptyFirst = AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 96 ++ AbiEntry.wordBytes 0 ++
      AbiEntry.wordBytes 2 ++ AbiEntry.wordBytes 300 ++ List.replicate 32 255 ∧
    emptyLast = AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 160 ++ AbiEntry.wordBytes 2 ++
      AbiEntry.wordBytes 300 ++ List.replicate 32 255 ++ AbiEntry.wordBytes 0 := by
  constructor
  · rw [bothEmpty,ArrayPairPacket.encoded_words]
    rfl
  constructor
  · rw [emptyFirst,ArrayPairPacket.encoded_words]
    simp only [MixedPacketControls.edgeWords,List.length_cons,List.length_nil,List.flatMap_nil,
      List.flatMap_cons,indexValue,wmod_of_lt (by decide +kernel : 300 < W),Int.toNat_natCast,
      MixedPacketControls.max_value,MixedPacketControls.max_bytes,List.append_nil,List.append_assoc]
  · rw [emptyLast,ArrayPairPacket.encoded_words]
    simp only [MixedPacketControls.edgeWords,List.length_cons,List.length_nil,List.flatMap_nil,
      List.flatMap_cons,indexValue,wmod_of_lt (by decide +kernel : 300 < W),Int.toNat_natCast,
      MixedPacketControls.max_value,MixedPacketControls.max_bytes,List.append_nil,List.append_assoc]

theorem boundary_lengths : bothEmpty.length = 128 ∧ emptyFirst.length = 192 ∧
    emptyLast.length = 192 ∧ fullWords.length = 224 ∧
    MixedPacketControls.edgeWords.length < AbiEntry.W ∧
    ArrayPairPacket.secondOffset [] = 96 ∧
    ArrayPairPacket.secondOffset [MixedPacketControls.edgeScalar] = 128 := by
  refine ⟨?_,?_,?_,?_,by decide +kernel,?_,?_⟩
  · rw [bothEmpty,ArrayPairPacket.encoded_length]
    rfl
  · rw [emptyFirst,ArrayPairPacket.encoded_length]
    rfl
  · rw [emptyLast,ArrayPairPacket.encoded_length]
    rfl
  · rw [fullWords,ArrayPairPacket.encoded_length]
    rfl
  · rw [ArrayPairPacket.second_offset]
    rfl
  · rw [ArrayPairPacket.second_offset]
    rfl

theorem boundaries_observed :
    (fullWords.drop 126).take 2 = [1,44] ∧ (fullWords.drop 128).take 32 = List.replicate 32 255 ∧
    (fullWords.drop 192).take 32 = List.replicate 32 255 ∧
    AbiEntry.load emptyFirst 32 = 96 ∧ AbiEntry.load emptyLast 32 = 160 ∧
    AbiEntry.load bothEmpty 32 = 96 ∧ AbiEntry.load emptyFirst 32 ≠ 160 := by
  rw [boundary_words,empties.1,empties.2.1,empties.2.2]
  repeat' constructor
  all_goals decide +kernel

theorem negative_packets :
    packet false ≠ AbiEntry.encodeArgs (ArrayPairPacket.values (lastWords false) firstWords) ∧
    packet false ≠ AbiEntry.encodeArgs (ArrayPairPacket.values
      [indexValue (wmod 7),indexValue (wmod 11)] (lastWords false)) ∧
    packet false ≠ AbiEntry.encodeArgs (ArrayPairPacket.values firstWords
      [indexValue (wmod 99),indexValue (wmod 101)]) ∧
    packet true ≠ AbiEntry.encodeArgs (WordArrayPacket.values firstWords) ∧
    packet true ≠ (AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 64 ++
      ArrayPairPacket.payload firstWords ++ ArrayPairPacket.payload firstWords) := by
  repeat' constructor
  all_goals decide +kernel

/-- Even an empty array retains its own length word, and full uint words cannot
be silently truncated to UInt8. These counterclaims have the positive baselines above. -/
theorem boundary_negatives :
    bothEmpty ≠ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 96 ∧
    AbiEntry.load emptyFirst 32 ≠ 64 ∧
    (fullWords.drop 96).take 32 ≠ AbiEntry.wordBytes 44 ∧
    (fullWords.drop 128).take 32 ≠ AbiEntry.wordBytes 255 := by
  rw [boundary_words,empties.1,empties.2.1]
  repeat' constructor
  all_goals decide +kernel

/-- Changing the SECOND array length to zero still preserves the complete
first prefix, including the second dynamic offset derived from the FIRST tail. -/
theorem empty_last_noninterference :
    (AbiEntry.encodeArgs (ArrayPairPacket.values firstWords [])).take 160 = (packet false).take 160 := by
  have unchanged := ArrayPairPacket.prefix_noninterference firstWords [] (lastWords false)
  rw [encoded,(offsets_and_order false).2.1] at unchanged
  exact unchanged

/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.encoded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.offsets_and_order' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms offsets_and_order
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.fixed_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_prefix
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.boundary_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary_words
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.empties' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empties
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.boundary_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary_lengths
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.boundaries_observed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundaries_observed
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.negative_packets' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms negative_packets
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.boundary_negatives' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary_negatives
/-- info: 'Solidity.Backend.AbiWorld.ArrayPairControls.empty_last_noninterference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_last_noninterference
end Solidity.Backend.AbiWorld.ArrayPairControls
