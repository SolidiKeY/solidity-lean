import Solidity.Backend.AbiWorld.NestedUintPacket
import Solidity.Semantics.AbiEntryChecks
import tests.«v13-abi-world».MixedCodecControls

/-! Complete pure codec controls; not universal admission or a nested heap. -/
namespace Solidity.Backend.AbiWorld.NestedControls
open Evm Evm.Memory AbiEntry.Checks

def u (n : Nat) : NestedUintPacket.UInt := indexValue (wmod n)
def mixed : List (List NestedUintPacket.UInt) := [[u 12,u 11],[u 23],[]]
def grown : List (List NestedUintPacket.UInt) := [[u 12,u 11],[u 23,u 29],[]]
def lastChanged : List (List NestedUintPacket.UInt) := [[u 12,u 11],[u 23],[u 300,u 0]]
def edge : List (List NestedUintPacket.UInt) := [[],MixedPacketControls.edgeWords,[u 0]]
def packet := AbiEntry.encodeArgs (NestedUintPacket.values mixed)
def grownPacket := AbiEntry.encodeArgs (NestedUintPacket.values grown)
def lastPacket := AbiEntry.encodeArgs (NestedUintPacket.values lastChanged)
def edgePacket := AbiEntry.encodeArgs (NestedUintPacket.values edge)
def emptyPacket := AbiEntry.encodeArgs (NestedUintPacket.values [])
def emptyInnerPacket := AbiEntry.encodeArgs (NestedUintPacket.values [[]])
def mixedInput : AbiEntry.Input := cd [32,3,96,192,256,2,12,11,1,23,0]

theorem mixed_encoding : packet = mixedInput.data.drop 4 := by
  rw [packet,NestedUintPacket.encoded_words]
  decide +kernel

theorem grown_encoding : grownPacket =
    (cd [32,3,96,192,288,2,12,11,2,23,29,0]).data.drop 4 := by
  rw [grownPacket,NestedUintPacket.encoded_words]
  decide +kernel

theorem last_encoding : lastPacket =
    (cd [32,3,96,192,256,2,12,11,1,23,2,300,0]).data.drop 4 := by
  rw [lastPacket,NestedUintPacket.encoded_words]
  decide +kernel

theorem edge_encoding : edgePacket =
    (cd [32,3,96,128,224,0,2,300,2^256-1,1,0]).data.drop 4 := by
  rw [edgePacket,NestedUintPacket.encoded_words]
  decide +kernel

theorem empty_encodings : emptyPacket = (cd [32,0]).data.drop 4 ∧
    emptyInnerPacket = (cd [32,1,32,0]).data.drop 4 := by
  constructor
  · rw [emptyPacket,NestedUintPacket.encoded_words]
    decide +kernel
  · rw [emptyInnerPacket,NestedUintPacket.encoded_words]
    decide +kernel

theorem exact_lengths : packet.length = 352 ∧ grownPacket.length = 384 ∧
    lastPacket.length = 416 ∧ edgePacket.length = 352 ∧ emptyPacket.length = 64 ∧
    emptyInnerPacket.length = 128 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [packet,NestedUintPacket.encoded_length]; rfl
  · rw [grownPacket,NestedUintPacket.encoded_length]; rfl
  · rw [lastPacket,NestedUintPacket.encoded_length]; rfl
  · rw [edgePacket,NestedUintPacket.encoded_length]; rfl
  · rw [emptyPacket,NestedUintPacket.encoded_length]; rfl
  · rw [emptyInnerPacket,NestedUintPacket.encoded_length]; rfl

/-- Positive baseline: byte64 is the element-head base; each offset is relative
there, rather than the outer array start at32 or the whole packet start at0. -/
theorem offsets_and_payloads :
    AbiEntry.load packet 0 = 32 ∧ AbiEntry.load packet 32 = 3 ∧
    AbiEntry.load packet 64 = 96 ∧ AbiEntry.load packet 96 = 192 ∧ AbiEntry.load packet 128 = 256 ∧
    AbiEntry.load packet (64 + 96) = 2 ∧ AbiEntry.load packet (64 + 192) = 1 ∧
    AbiEntry.load packet (64 + 256) = 0 ∧
    (packet.drop 160).take 96 = (cd [2,12,11]).data.drop 4 ∧
    (packet.drop 256).take 64 = (cd [1,23]).data.drop 4 ∧
    packet.drop 320 = (cd [0]).data.drop 4 ∧
    352 < AbiEntry.W ∧ mixed.length < AbiEntry.W := by
  rw [mixed_encoding]
  decide +kernel

/-- Last growth preserves ALL preceding heads/tails; middle growth preserves
only earlier heads/tails and changes the later third-head offset. -/
theorem noninterference : packet.take 320 = lastPacket.take 320 ∧
    packet.take 128 = grownPacket.take 128 ∧
    (packet.drop 160).take 96 = (grownPacket.drop 160).take 96 ∧
    AbiEntry.load grownPacket 128 = 288 ∧ AbiEntry.load packet 128 ≠ AbiEntry.load grownPacket 128 := by
  constructor
  · have unchanged := NestedUintPacket.last_noninterference [[u 12,u 11],[u 23]] [] [u 300,u 0]
    have prefix_size : 64 + 32 * ([[u 12,u 11],[u 23]].length + 1) +
        (NestedUintPacket.payloads [[u 12,u 11],[u 23]]).flatten.length = 320 := by
      rw [NestedUintPacket.payload_total_length]
      rfl
    rw [prefix_size] at unchanged
    exact unchanged
  constructor
  · rw [mixed_encoding,grown_encoding]
    decide +kernel
  · rw [mixed_encoding,grown_encoding]
    decide +kernel

/-- Full32byte300/max data and embedded zero; no UInt8 range restriction. -/
theorem full_words : (edgePacket.drop 254).take 2 = [1,44] ∧
    (edgePacket.drop 256).take 32 = List.replicate 32 255 ∧ AbiEntry.load edgePacket 320 = 0 ∧
    (edgePacket.drop 224).take 32 ≠ AbiEntry.wordBytes 44 ∧
    (edgePacket.drop 256).take 32 ≠ AbiEntry.wordBytes 255 := by
  rw [edge_encoding]
  decide +kernel

/-- Counterclaims retain the complete positive packet above. No malformed
input is classified as revert/blocked merely from these byte inequalities. -/
theorem negative_claims :
    AbiEntry.load packet (32 + AbiEntry.load packet 64) ≠ 2 ∧
    AbiEntry.load packet 64 ≠ 128 ∧ AbiEntry.load packet 64 ≠ 160 ∧
    packet ≠ (cd [32,3,128,224,288,2,12,11,1,23,0]).data.drop 4 ∧
    packet ≠ (cd [32,96,192,256,2,12,11,1,23,0]).data.drop 4 ∧
    packet ≠ (cd [32,3,96,192,256,12,11,1,23,0]).data.drop 4 ∧
    packet ≠ AbiEntry.encodeArgs (NestedUintPacket.values [[u 23],[u 12,u 11],[]]) ∧
    emptyInnerPacket ≠ emptyPacket := by
  rw [mixed_encoding,empty_encodings.1,empty_encodings.2]
  decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.NestedControls.mixed_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_encoding
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.grown_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grown_encoding
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.last_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms last_encoding
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.edge_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms edge_encoding
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.empty_encodings' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_encodings
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.exact_lengths' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_lengths
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.offsets_and_payloads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms offsets_and_payloads
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.noninterference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms noninterference
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.full_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_words
/-- info: 'Solidity.Backend.AbiWorld.NestedControls.negative_claims' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms negative_claims
end Solidity.Backend.AbiWorld.NestedControls
