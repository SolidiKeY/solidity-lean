import Solidity.Backend.AbiWorld.MixedPacket
/-! Pure published codec controls, distinct from compiled/source admission. -/
namespace Solidity.Backend.AbiWorld.MixedPacketControls
open Evm Evm.Memory

def packet : List UInt8 := AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 42 ++
  AbiEntry.wordBytes 2 ++ AbiEntry.wordBytes 12 ++ AbiEntry.wordBytes 11

/-- Pure actual-codec fixtures: empty, full-word300, and maximum uint256.
These are not claims of source ABI profile admission or compiled execution. -/
def edgeScalar : PrimTy.uint.Denote := indexValue (wmod (W - 1))
def edgeWords : List PrimTy.uint.Denote := [indexValue (wmod 300),edgeScalar]
def boundaryPacket : List UInt8 := AbiEntry.encodeArgs (MixedPacket.values edgeWords edgeScalar)

theorem max_value : edgeScalar.val.toNat = W - 1 := by
  simp only [edgeScalar,indexValue,wmod_of_lt (by decide +kernel : W - 1 < W),Int.toNat_natCast]

theorem max_bytes : AbiEntry.wordBytes (W - 1) = List.replicate 32 255 := by decide +kernel

theorem boundary_encoding : boundaryPacket = AbiEntry.wordBytes 64 ++ List.replicate 32 255 ++
    AbiEntry.wordBytes 2 ++ AbiEntry.wordBytes 300 ++ List.replicate 32 255 := by
  rw [boundaryPacket,MixedPacket.encoded_values]
  simp only [edgeWords,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
    indexValue,wmod_of_lt (by decide +kernel : 300 < W),Int.toNat_natCast,max_value,
    List.append_nil,max_bytes,List.append_assoc]

theorem boundaries :
    AbiEntry.encodeArgs (MixedPacket.values [] (indexValue (wmod 42))) =
      AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 42 ++ AbiEntry.wordBytes 0 ∧
    (AbiEntry.encodeArgs (MixedPacket.values [] edgeScalar)).length = 96 ∧
    boundaryPacket = AbiEntry.wordBytes 64 ++ List.replicate 32 255 ++ AbiEntry.wordBytes 2 ++
      AbiEntry.wordBytes 300 ++ List.replicate 32 255 ∧
    boundaryPacket.length = 160 ∧
    (boundaryPacket.drop 126).take 2 = [1,44] ∧
    edgeWords.length < AbiEntry.W := by
  refine ⟨?_,?_,boundary_encoding,?_,?_,?_⟩
  · rw [MixedPacket.encoded_values]
    decide +kernel
  · rw [MixedPacket.encoded_length]
    rfl
  · rw [boundaryPacket,MixedPacket.encoded_length]
    rfl
  · rw [boundary_encoding]
    decide +kernel
  · decide +kernel

def swapped : AbiEntry.Vals [MixedPacket.ScalarShape,WordArrayPacket.Shape] :=
  .cons (.word (WordArrayPacket.uintWord (indexValue (wmod 42))))
    (.cons (.array (WordArrayPacket.sequence [indexValue (wmod 12),indexValue (wmod 11)])) .nil)

theorem ordered_negatives :
    packet.length = 160 ∧ packet.take 32 = AbiEntry.wordBytes 64 ∧
    (packet.drop 32).take 32 = AbiEntry.wordBytes 42 ∧
    packet.drop 64 = AbiEntry.wordBytes 2 ++ AbiEntry.wordBytes 12 ++ AbiEntry.wordBytes 11 ∧
    packet.take 32 ≠ AbiEntry.wordBytes 32 ∧ packet ≠ AbiEntry.encodeArgs swapped ∧
    packet ≠ AbiEntry.encodeArgs (MixedPacket.values [indexValue (wmod 7),indexValue (wmod 11)] (indexValue (wmod 42))) ∧
    packet ≠ AbiEntry.encodeArgs (MixedPacket.values [indexValue (wmod 12),indexValue (wmod 11)] (indexValue (wmod 11))) ∧
    packet ≠ AbiEntry.encodeArgs (MixedPacket.values [indexValue (wmod 99),indexValue (wmod 101)] (indexValue (wmod 42))) := by
  repeat' constructor
  all_goals decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.max_value' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms max_value
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.max_bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms max_bytes
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.boundary_encoding' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms boundary_encoding
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.boundaries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundaries
/-- info: 'Solidity.Backend.AbiWorld.MixedPacketControls.ordered_negatives' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms ordered_negatives
end Solidity.Backend.AbiWorld.MixedPacketControls
