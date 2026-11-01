import Solidity.Backend.AbiWorld.CanonicalReadback
import tests.«v13-abi-world».NestedEntryControls

/-! Actual generic theorem applications plus finite negative controls.
No new external compiler/EVM agreement or nested entry simulation is asserted. -/
namespace Solidity.Backend.AbiWorld.CanonicalControls
open AbiEntry CanonicalReadback
open Evm Evm.Memory

def selector : List UInt8 := [222,0,173,190]
def trailing : List UInt8 := [19,0,255]
def words : List UInt := MixedPacketControls.edgeWords ++ [indexValue (wmod 0)]
def packet := encodeArgs (WordArrayPacket.values words)
def sample := input words selector trailing 128
def empty := input [] selector trailing 128
def swappedWords : List UInt := [indexValue (wmod 0),MixedPacketControls.edgeScalar,indexValue (wmod 300)]
def staleWords : List UInt := [indexValue (wmod 7),MixedPacketControls.edgeScalar,indexValue (wmod 0)]
def swapped := input swappedWords selector trailing 128
def stale := input staleWords selector trailing 128

def prefixBytes : List UInt8 := [9,0,255]
def suffixBytes : List UInt8 := [17,0]
def embedded := prefixBytes ++ AbiEntry.wordBytes 300 ++ suffixBytes
def embeddedMax := prefixBytes ++ AbiEntry.wordBytes (AbiEntry.W - 1) ++ suffixBytes

/-- These actual verdict identities instantiate the generic proof, not eval
of a desired fixed typed value or a codec-only assumed simulation. -/
theorem full_roundtrip :
    verdict sample 7 (params .memory) = .run (WordArrayPacket.values words) ∧
    verdict sample 7 (params .calldata) = .run (WordArrayPacket.values words) ∧
    EntryTransport.bodyObservation sample 7 (params .memory) encodeArgs = some packet ∧
    EntryTransport.bodyObservation sample 7 (params .calldata) encodeArgs = some packet ∧
    cval sample 6 WordArrayPacket.Shape 68 words.length = .ok (.array (WordArrayPacket.sequence words)) :=
  roundtrip words selector trailing 128 7 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem empty_roundtrip :
    verdict empty 4 (params .memory) = .run (WordArrayPacket.values []) ∧
    verdict empty 4 (params .calldata) = .run (WordArrayPacket.values []) ∧
    EntryTransport.bodyObservation empty 4 (params .memory) encodeArgs =
      some (encodeArgs (WordArrayPacket.values [])) := by
  have h := roundtrip [] selector trailing 128 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem changed_inputs_accepted :
    verdict swapped 7 (params .memory) = .run (WordArrayPacket.values swappedWords) ∧
    verdict stale 7 (params .calldata) = .run (WordArrayPacket.values staleWords) :=
  ⟨memory_verdict swappedWords selector trailing 128 7 (by decide +kernel) (by decide +kernel) (by decide +kernel),
   calldata_verdict staleWords selector trailing 128 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem ordered : packet = (Checks.cd [32,3,300,AbiEntry.W-1,0]).data.drop 4 ∧
    packet.length = 160 ∧ sample.data = selector ++ packet ++ trailing ∧ sample.size = 167 ∧
    enter sample 7 (params .memory) 0 0 =
      .ok (.cons (.val (.array (WordArrayPacket.sequence words))) .nil,128) := by
  refine ⟨?_,?_,rfl,?_,?_⟩
  · decide +kernel
  · rw [packet,WordArrayPacket.encoded_values]
    simp only [List.length_append,MixedPacket.word_length,words_length]
    rfl
  · rw [sample,input_size]
    rfl
  · exact (memory_entry words selector trailing 128 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).1

theorem word_baselines : load embedded prefixBytes.length = 300 ∧
    load embeddedMax prefixBytes.length = AbiEntry.W - 1 ∧
    (embedded.drop prefixBytes.length).take 32 = AbiEntry.wordBytes 300 ∧
    embedded.length = 37 ∧ embeddedMax.length = 37 := by
  exact ⟨load_word _ _ 300 (by decide +kernel),load_word _ _ _ (by decide +kernel),
    by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- Allocating exactly to lim is accepted by the ORIGINAL allocator. -/
theorem allocation_boundary :
    verdict (input words selector trailing (lim - 128)) 7 (params .memory) =
      .run (WordArrayPacket.values words) ∧
    enter (input words selector trailing (lim - 128)) 7 (params .memory) 0 0 =
      .ok (.cons (.val (.array (WordArrayPacket.sequence words))) .nil,128) ∧
    (lim - 128) + 128 = lim :=
  ⟨memory_verdict words selector trailing _ 7 (by decide +kernel) (by decide +kernel) (by decide +kernel),
   (memory_entry words selector trailing _ 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)).1,
   by decide +kernel⟩

def wrongOffset := Checks.cd [64,3,300,AbiEntry.W-1,0]
def missingLength : Input := ⟨selector ++ AbiEntry.wordBytes 32,128⟩
def truncated : Input := ⟨selector ++ packet.take 159,128⟩
def tooTight := input words selector trailing (lim - 127)
def tightTruncated : Input := ⟨truncated.data,lim - 127⟩

private theorem failed {ε α : Type} (x : Except ε α) (e : ε)
    (h : (match x with | .error a => some a | .ok _ => none) = some e) : x = .error e := by
  cases x with
  | error a => cases h; rfl
  | ok a => cases h

/-- These are actual classified entry failures, unlike a false byte equality. -/
theorem rejected_entries : entry wrongOffset 7 (params .memory) = .error .revert ∧
    entry missingLength 7 (params .memory) = .error .revert ∧
    entry truncated 7 (params .memory) = .error .revert := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

/-- Possible allocation failure, fuel refusal and bounds reverts remain
separate. Allocation happens before the element-region bounds check. -/
theorem refusals :
    (verdict tooTight 7 (params .memory)).kind = "blocked: possible Panic(0x41) allocation failure in memory decoding" ∧
    (verdict tightTruncated 7 (params .memory)).kind = "blocked: possible Panic(0x41) allocation failure in memory decoding" ∧
    (verdict sample 4 (params .memory)).kind = "blocked: ABI decoder fuel exhausted" ∧
    (verdict sample 0 (params .calldata)).kind = "blocked: ABI decoder fuel exhausted" ∧
    EntryTransport.rejection tooTight 7 (params .memory) 17 = none ∧
    EntryTransport.rejection sample 4 (params .memory) 17 = none := by decide +kernel

def machine : Failure.Slice.Machine := ⟨[⟨77,by decide +kernel⟩],fun _ => 0xa5⟩
def suffix : Program := [.op .RETURN]

/-- The actual truncated-input entry failure consumes the checked empty-byte
REVERT adapter, retaining its real Fits/stack premises and original suffix. -/
theorem truncated_emitted : EntryTransport.runRejection truncated 7 (params .memory) 17 suffix machine =
    some (machine,some (.revert [])) :=
  EntryTransport.entry_revert_exec truncated 7 (params .memory) 17 suffix machine rejected_entries.2.2
    ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩ (by decide +kernel)

/-- Positive baselines above distinguish accepted changed values from refusals;
wrong offset/order/truncated-byte claims do not become admission restrictions. -/
theorem negative_observations : load embedded (prefixBytes.length + 1) ≠ 300 ∧
    AbiEntry.wordBytes 300 ≠ AbiEntry.wordBytes 44 ∧
    packet ≠ encodeArgs (WordArrayPacket.values swappedWords) ∧
    packet ≠ encodeArgs (WordArrayPacket.values staleWords) ∧
    packet ≠ packet.take 159 ∧
    load (prefixBytes ++ AbiEntry.wordBytes AbiEntry.W ++ suffixBytes) prefixBytes.length = 0 ∧
    load (prefixBytes ++ AbiEntry.wordBytes AbiEntry.W ++ suffixBytes) prefixBytes.length ≠ AbiEntry.W := by decide +kernel

/-- Actual selected inner decoder fragment uses the real nested byte160 base
and an explicit cursor128; this is NOT a whole nested entry theorem. -/
theorem nested_fragment :
    mdec ⟨NestedControls.packet,128⟩ 5 WordArrayPacket.Shape 160 128 =
      .ok (.array (WordArrayPacket.sequence [NestedControls.u 12,NestedControls.u 11]),224) :=
  nested_inner [] [NestedControls.u 12,NestedControls.u 11] [[NestedControls.u 23],[]]
    ⟨NestedControls.packet,128⟩ 128 5 rfl (by decide +kernel) (by decide +kernel)

/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.full_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_roundtrip
/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.empty_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_roundtrip
/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.changed_inputs_accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_inputs_accepted
/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ordered
/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.word_baselines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_baselines
/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.allocation_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_boundary
/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.rejected_entries' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_entries
/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.refusals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refusals
/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.truncated_emitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms truncated_emitted
/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.negative_observations' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms negative_observations
/-- info: 'Solidity.Backend.AbiWorld.CanonicalControls.nested_fragment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_fragment
end Solidity.Backend.AbiWorld.CanonicalControls
