import Solidity.Backend.AbiWorld.BytesReadback
import tests.«v13-abi-world».NestedOuterControls

/-! Actual generic byte-string entry applications and failure-order controls.
No external/native agreement, runtime byte encoder or O1 phase contract is asserted. -/
namespace Solidity.Backend.AbiWorld.BytesEntryControls
open AbiEntry BytesReadback

def selector := CanonicalControls.selector
def trailing := CanonicalControls.trailing
def mixed : List UInt8 := [0,255,17,0,128]
def b31 : List UInt8 := List.replicate 29 0 ++ [255,7]
def b32 : List UInt8 := List.replicate 30 0 ++ [255,7]
def b33 : List UInt8 := List.replicate 31 0 ++ [255,7]
def packet (bs : List UInt8) := encodeArgs (values bs)
def sample := input mixed selector trailing 128
def i31 := input b31 selector trailing 128
def i32 := input b32 selector trailing 128
def i33 := input b33 selector trailing 128

theorem counts : allocationBytes [] = 32 ∧ allocationBytes [0] = 64 ∧
    allocationBytes b31 = 64 ∧ allocationBytes b32 = 64 ∧ allocationBytes b33 = 96 ∧
    (packet []).length = 64 ∧ (packet b31).length = 96 ∧ (packet b32).length = 96 ∧
    (packet b33).length = 128 ∧ i31.size = 103 ∧ i32.size = 103 ∧ i33.size = 135 := by decide +kernel

/-- Exact typed values, complete body bytes and the real checked lazy read
instantiate the generic theorem, not a desired-verdict fixed computation. -/
theorem full_roundtrip : verdict i33 2 (params .memory) = .run (values b33) ∧
    verdict i33 2 (params .calldata) = .run (values b33) ∧
    EntryTransport.bodyObservation i33 2 (params .memory) encodeArgs = some (packet b33) ∧
    EntryTransport.bodyObservation i33 2 (params .calldata) encodeArgs = some (packet b33) ∧
    cval i33 1 .bytes 68 b33.length = .ok (.bytes b33) :=
  roundtrip b33 selector trailing 128 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem family : ∀ bs ∈ [[],[0],[255],mixed,b31,b32,b33],
    verdict (input bs selector trailing 128) 2 (params .memory) = .run (values bs) ∧
    verdict (input bs selector trailing 128) 2 (params .calldata) = .run (values bs) := by
  intro bs hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨memory_verdict _ selector trailing 128 2 (by decide +kernel) (by decide +kernel) (by decide +kernel),
    calldata_verdict _ selector trailing 128 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem exact_padding : (packet b31).drop 95 = [0] ∧ (packet b32).drop 96 = [] ∧
    (packet b33).drop 97 = List.replicate 31 0 ∧
    ((packet b33).drop 64).take 33 = b33 ∧ packet b33 = AbiEntry.wordBytes 32 ++
      AbiEntry.wordBytes 33 ++ b33 ++ List.replicate 31 0 := by
  exact ⟨exact_zeros b31,exact_zeros b32,exact_zeros b33,exact_payload b33,encoded b33⟩

theorem allocation_trace :
    enter i31 2 (params .memory) 0 0 = .ok (.cons (.val (.bytes b31)) .nil,64) ∧
    enter i32 2 (params .memory) 0 0 = .ok (.cons (.val (.bytes b32)) .nil,64) ∧
    enter i33 2 (params .memory) 0 0 = .ok (.cons (.val (.bytes b33)) .nil,96) := by
  have h31 := (memory_entry b31 selector trailing 128 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  have h32 := (memory_entry b32 selector trailing 128 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  have h33 := (memory_entry b33 selector trailing 128 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  exact ⟨h31,h32,h33⟩

def boundary := input b33 selector trailing (lim - 96)
def tooTight := input b33 selector trailing (lim - 95)

theorem allocation_boundary : verdict boundary 2 (params .memory) = .run (values b33) ∧
    enter boundary 2 (params .memory) 0 0 = .ok (.cons (.val (.bytes b33)) .nil,96) ∧
    (lim - 96) + 96 = lim :=
  ⟨memory_verdict b33 selector trailing _ 2 (by decide +kernel) (by decide +kernel) (by decide +kernel),
   (memory_entry b33 selector trailing _ 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)).1,
   by decide +kernel⟩

def unpadded : Input := ⟨selector ++ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 33 ++ b33,128⟩
def dirty : Input := ⟨selector ++ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 33 ++ b33 ++
    List.replicate 31 170 ++ trailing,128⟩

/-- Generic actual mdec allows arbitrary following bytes. Padding is not a
content validator and neither dirty nor absent padding is silently excluded. -/
theorem dirty_decoder : mdec dirty 1 .bytes 36 0 = .ok (.bytes b33,96) := by
  have len33 : b33.length = 33 := by decide +kernel
  exact mdec_bytes b33 dirty (selector ++ AbiEntry.wordBytes 32) (List.replicate 31 170 ++ trailing) 0 1
    (by simp only [dirty,List.append_assoc,len33]) (by decide +kernel) (by decide +kernel)

theorem accepted_padding :
    EntryTransport.bodyObservation unpadded 2 (params .memory) encodeArgs = some (packet b33) ∧
    EntryTransport.bodyObservation unpadded 2 (params .calldata) encodeArgs = some (packet b33) ∧
    EntryTransport.bodyObservation dirty 2 (params .memory) encodeArgs = some (packet b33) ∧
    EntryTransport.bodyObservation dirty 2 (params .calldata) encodeArgs = some (packet b33) := by decide +kernel

def wrongOffset := Checks.cd [64,33] b33
def missingLength : Input := ⟨selector ++ AbiEntry.wordBytes 32,128⟩
def shortHeader : Input := ⟨selector ++ AbiEntry.wordBytes 32 ++ (AbiEntry.wordBytes 33).take 31,lim - 31⟩
def shortPayload : Input := ⟨selector ++ (packet b33).take 96,128⟩
def tightPayload : Input := ⟨shortPayload.data,lim - 95⟩
def reading : List Param := [{shape := .bytes,loc := .calldata,readsOnly := true}]

private theorem failed {ε α : Type} (x : Except ε α) (e : ε)
    (h : (match x with | .error a => some a | .ok _ => none) = some e) : x = .error e := by
  cases x with
  | error a => cases h; rfl
  | ok a => cases h

theorem rejected_entries : entry wrongOffset 2 (params .memory) = .error .revert ∧
    entry missingLength 2 (params .memory) = .error .revert ∧
    entry shortHeader 2 (params .memory) = .error .revert ∧
    entry shortPayload 2 (params .memory) = .error .revert ∧
    entry shortPayload 2 (params .calldata) = .error .revert := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),
    failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

/-- Even the minimum bytes-object allocation would fail in this input;
the actual incomplete-header check must therefore happen first. -/
theorem header_priority : entry shortHeader 2 (params .memory) = .error .revert ∧
    alloc shortHeader 0 32 = .error .panic :=
  ⟨rejected_entries.2.2.1,failed _ _ (by decide +kernel)⟩

/-- Preserve header-before-allocation-before-region and all named refusals.
Bytes have no per-byte cleanup: checked reference bounds occur at entry. The
readsOnly result is intrinsic classification, not source permission to encode it. -/
theorem failure_order :
    (verdict tooTight 2 (params .memory)).kind = "blocked: possible Panic(0x41) allocation failure in memory decoding" ∧
    (verdict tightPayload 2 (params .memory)).kind = "blocked: possible Panic(0x41) allocation failure in memory decoding" ∧
    (verdict shortHeader 2 (params .memory)).kind = "revert" ∧
    (verdict shortPayload 2 (params .calldata)).kind = "revert" ∧
    (verdict tooTight 2 (params .calldata)).kind = "blocked: calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics" ∧
    (verdict tooTight 2 reading).kind = "run" ∧
    (verdict i33 1 (params .memory)).kind = "blocked: ABI decoder fuel exhausted" ∧
    (verdict i33 1 (params .calldata)).kind = "blocked: ABI decoder fuel exhausted" ∧
    EntryTransport.rejection tooTight 2 (params .memory) 17 = none ∧
    EntryTransport.rejection i33 1 (params .memory) 17 = none := by decide +kernel

/-- Raw zero-extension is not a checked entry witness. All byte/order claims
below have the positive generic identity and accepted-body baselines above. -/
theorem negative_observations : bytesAt shortPayload.data 68 33 = List.replicate 31 0 ++ [255,0] ∧
    packet b33 ≠ (packet b33).take 96 ∧ packet b33 ≠ packet b32 ∧
    packet mixed ≠ packet mixed.reverse ∧ packet mixed ≠ packet [0,255,18,0,128] ∧
    (packet b33).drop 97 ≠ List.replicate 31 170 := by decide +kernel

/-- Equal padded tails do not imply equal typed bytes: length words matter. -/
theorem length_identity : Semantics.pad32 [17] = Semantics.pad32 [17,0] ∧
    packet [17] ≠ packet [17,0] ∧
    verdict (input [17] selector trailing 128) 2 (params .memory) = .run (values [17]) ∧
    verdict (input [17,0] selector trailing 128) 2 (params .calldata) = .run (values [17,0]) :=
  ⟨by decide +kernel,by decide +kernel,
   memory_verdict _ selector trailing 128 2 (by decide +kernel) (by decide +kernel) (by decide +kernel),
   calldata_verdict _ selector trailing 128 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem short_payload_emitted : EntryTransport.runRejection shortPayload 2 (params .memory) 17
    CanonicalControls.suffix CanonicalControls.machine =
      some (CanonicalControls.machine,some (.revert [])) :=
  EntryTransport.entry_revert_exec shortPayload 2 (params .memory) 17 CanonicalControls.suffix
    CanonicalControls.machine rejected_entries.2.2.2.1 ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩
    (by decide +kernel)

/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.counts' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms counts
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.full_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_roundtrip
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms family
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.exact_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_padding
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.allocation_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_trace
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.allocation_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_boundary
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.dirty_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_decoder
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.accepted_padding' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms accepted_padding
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.rejected_entries' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms rejected_entries
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.header_priority' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms header_priority
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.failure_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failure_order
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.negative_observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms negative_observations
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.length_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms length_identity
/-- info: 'Solidity.Backend.AbiWorld.BytesEntryControls.short_payload_emitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_payload_emitted
end Solidity.Backend.AbiWorld.BytesEntryControls
