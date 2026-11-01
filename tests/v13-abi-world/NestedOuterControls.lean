import Solidity.Backend.AbiWorld.NestedReadback
import tests.«v13-abi-world».CanonicalControls

/-! Actual generic nested readback applications and failure-order controls.
These are intrinsic canonical decoder facts, not a runtime/source/native or
world-memory compiler simulation. Prior complete observations stay unchanged. -/
namespace Solidity.Backend.AbiWorld.NestedOuterControls
open AbiEntry NestedReadback

def selector := CanonicalControls.selector
def trailing := CanonicalControls.trailing
def rows := NestedControls.mixed
def edgeRows := NestedControls.edge
def repeatedRows := [[NestedControls.u 12,NestedControls.u 11],[NestedControls.u 12,NestedControls.u 11]]
def swappedRows := [[NestedControls.u 23],[NestedControls.u 12,NestedControls.u 11],[]]
def staleRows := [[NestedControls.u 7,NestedControls.u 11],[NestedControls.u 23],[]]
def packet := encodeArgs (NestedUintPacket.values rows)
def sample := input rows selector trailing 128
def edge := input edgeRows selector trailing 128
def empty := input [] selector trailing 128
def oneEmpty := input [[]] selector trailing 128
def twoEmpty := input [[],[]] selector trailing 128
def repeated := input repeatedRows selector trailing 128
def swapped := input swappedRows selector trailing 128
def stale := input staleRows selector trailing 128

theorem counts : allocationBytes rows = 320 ∧ allocationBytes edgeRows = 320 ∧
    allocationBytes [] = 32 ∧ allocationBytes [[]] = 96 ∧ allocationBytes [[],[]] = 160 ∧
    allocationBytes repeatedRows = 288 ∧ packet.length = 352 ∧ sample.size = 359 := by decide +kernel

/-- Full typed identity, actual body observations and real lazy read from one
application of the generic proof, not desired-verdict kernel evaluation. -/
theorem full_roundtrip : verdict sample 12 (params .memory) = .run (NestedUintPacket.values rows) ∧
    verdict sample 12 (params .calldata) = .run (NestedUintPacket.values rows) ∧
    EntryTransport.bodyObservation sample 12 (params .memory) encodeArgs = some packet ∧
    EntryTransport.bodyObservation sample 12 (params .calldata) encodeArgs = some packet ∧
    cval sample 11 NestedUintPacket.Shape 68 rows.length = .ok (NestedUintPacket.value rows) :=
  roundtrip rows selector trailing 128 12 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Empty outer/inner arrays and equal inner values are admitted by the same
proof. Equal values require neither an ABI nor runtime disjointness premise. -/
theorem empty_and_fullword :
    verdict empty 6 (params .memory) = .run (NestedUintPacket.values []) ∧
    verdict oneEmpty 7 (params .calldata) = .run (NestedUintPacket.values [[]]) ∧
    verdict twoEmpty 8 (params .memory) = .run (NestedUintPacket.values [[],[]]) ∧
    verdict repeated 12 (params .calldata) = .run (NestedUintPacket.values repeatedRows) ∧
    verdict edge 12 (params .memory) = .run (NestedUintPacket.values edgeRows) :=
  ⟨memory_verdict [] selector trailing 128 6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   calldata_verdict [[]] selector trailing 128 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   memory_verdict [[],[]] selector trailing 128 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   calldata_verdict repeatedRows selector trailing 128 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   memory_verdict edgeRows selector trailing 128 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

/-- The same reached decoder input threads outer128, first-inner224,
second-inner288, final320; each remaining sequence has its actual head index. -/
theorem allocation_trace :
    enter sample 12 (params .memory) 0 0 = .ok (.cons (.val (NestedUintPacket.value rows)) .nil,320) ∧
    mseq sample 10 WordArrayPacket.Shape 68 0 3 128 = .ok (NestedUintPacket.sequence rows,320) ∧
    mseq sample 9 WordArrayPacket.Shape 68 1 2 224 =
      .ok (NestedUintPacket.sequence [[NestedControls.u 23],[]],320) ∧
    mseq sample 8 WordArrayPacket.Shape 68 2 1 288 = .ok (NestedUintPacket.sequence [[]],320) ∧
    mseq sample 7 WordArrayPacket.Shape 68 3 0 320 = .ok (NestedUintPacket.sequence [],320) := by
  have im : innerBytes rows = 192 := by rw [inner_formula]; rfl
  have it : innerBytes [[NestedControls.u 23],[]] = 96 := by rw [inner_formula]; rfl
  have il : innerBytes [[]] = 32 := by rw [inner_formula]; rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := (memory_entry rows selector trailing 128 12 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).1
    simpa only [counts.1] using h
  · have h := outer_sequence rows [] sample selector trailing 128 10 rfl
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    simpa only [im] using h
  · have h := outer_sequence [[NestedControls.u 23],[]] [[NestedControls.u 12,NestedControls.u 11]]
      sample selector trailing 224 9 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    simpa only [it] using h
  · have h := outer_sequence [[]] [[NestedControls.u 12,NestedControls.u 11],[NestedControls.u 23]]
      sample selector trailing 288 8 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    simpa only [il] using h
  · rfl

/-- Preserve the exact old input/fuel/parameters before strengthening its
previous encoded-byte witness to actual canonical typed identity. -/
theorem original_input : NestedControls.mixedInput = input rows [0,0,0,0] [] (2^32) := by
  apply congrArg (fun d => (⟨d,2^32⟩ : Input))
  decide +kernel

theorem original_verdict (lazy : Bool) :
    verdict NestedControls.mixedInput 64 (NestedControls.params lazy) = .run (NestedUintPacket.values rows) := by
  rw [original_input]
  cases lazy with
  | false =>
    exact memory_verdict rows [0,0,0,0] [] (2^32) 64 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  | true =>
    exact calldata_verdict rows [0,0,0,0] [] (2^32) 64 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem original_values_identity (lazy : Bool) :
    NestedControls.actualValues lazy = NestedUintPacket.values rows := by
  have h := NestedControls.accepted lazy
  rw [original_verdict lazy] at h
  exact (Verdict.run.inj h).symm

/-- The earlier conditional layout theorem now has a real discharged exact
verdict premise at its original input/fuel/location, with actual body values. -/
theorem original_layout (lazy : Bool) : ∃ es,
    entry NestedControls.mixedInput 64 (NestedControls.params lazy) = .ok es ∧
    bodyValues NestedControls.mixedInput 64 (NestedControls.params lazy) es 0 = .ok (NestedUintPacket.values rows) ∧
    EntryTransport.bodyObservation NestedControls.mixedInput 64 (NestedControls.params lazy) encodeArgs =
      some (AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes rows.length ++
        (List.range rows.length).flatMap (fun i => AbiEntry.wordBytes
          (32 * rows.length + ((NestedUintPacket.payloads rows).take i).flatten.length)) ++
        (NestedUintPacket.payloads rows).flatten) :=
  NestedUintPacket.accepted_layout NestedControls.mixedInput 64 (NestedControls.location lazy) rows (original_verdict lazy)

def boundary := input rows selector trailing (lim - 320)
def tooTight := input rows selector trailing (lim - 319)

theorem allocation_boundary :
    verdict boundary 12 (params .memory) = .run (NestedUintPacket.values rows) ∧
    enter boundary 12 (params .memory) 0 0 = .ok (.cons (.val (NestedUintPacket.value rows)) .nil,320) ∧
    (lim - 320) + 320 = lim := by
  refine ⟨memory_verdict rows selector trailing _ 12 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel),?_,by decide +kernel⟩
  have h := (memory_entry rows selector trailing (lim - 320) 12 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).1
  simpa only [counts.1] using h

def wrongBase := Checks.cd [32,3,128,192,256,2,12,11,1,23,0]
def missingLength : Input := ⟨selector ++ AbiEntry.wordBytes 32,128⟩
def truncatedHeader : Input := ⟨selector ++ packet.take 351,128⟩
def tightHeader : Input := ⟨truncatedHeader.data,lim - 319⟩
def truncatedPayload : Input := ⟨selector ++ (encodeArgs (NestedUintPacket.values edgeRows)).take 351,128⟩
def tightPayload : Input := ⟨truncatedPayload.data,lim - 319⟩

private theorem failed {ε α : Type} (x : Except ε α) (e : ε)
    (h : (match x with | .error a => some a | .ok _ => none) = some e) : x = .error e := by
  cases x with
  | error a => cases h; rfl
  | ok a => cases h

theorem rejected_entries : entry wrongBase 12 (params .memory) = .error .revert ∧
    entry missingLength 12 (params .memory) = .error .revert ∧
    entry truncatedHeader 12 (params .memory) = .error .revert ∧
    entry tightHeader 12 (params .memory) = .error .revert ∧
    entry truncatedPayload 12 (params .memory) = .error .revert := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),
    failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

/-- Header checks still precede allocation; allocation still precedes element
region checks. Possible Panic and fuel failures remain blocked, not reverts. -/
theorem failure_order :
    (verdict tooTight 12 (params .memory)).kind = "blocked: possible Panic(0x41) allocation failure in memory decoding" ∧
    (verdict tightPayload 12 (params .memory)).kind = "blocked: possible Panic(0x41) allocation failure in memory decoding" ∧
    (verdict tightHeader 12 (params .memory)).kind = "revert" ∧
    (verdict sample 6 (params .memory)).kind = "blocked: ABI decoder fuel exhausted" ∧
    (verdict sample 0 (params .calldata)).kind = "blocked: ABI decoder fuel exhausted" ∧
    (verdict wrongBase 12 (params .calldata)).kind = "blocked: calldata element fails only on access: needs access-time calldata semantics" ∧
    EntryTransport.rejection tooTight 12 (params .memory) 17 = none ∧
    EntryTransport.rejection sample 6 (params .memory) 17 = none := by decide +kernel

/-- Changed ordering/values have positive actual acceptance before byte
counterclaims; they are not silently excluded by the canonical theorem. -/
theorem changed_accepted : verdict swapped 12 (params .memory) = .run (NestedUintPacket.values swappedRows) ∧
    verdict stale 12 (params .calldata) = .run (NestedUintPacket.values staleRows) :=
  ⟨memory_verdict swappedRows selector trailing 128 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   calldata_verdict staleRows selector trailing 128 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem byte_controls : load sample.data 68 = 96 ∧ load sample.data 164 = 2 ∧
    load sample.data (36 + load sample.data 68) ≠ 2 ∧
    packet ≠ encodeArgs (NestedUintPacket.values swappedRows) ∧
    packet ≠ encodeArgs (NestedUintPacket.values staleRows) ∧ packet ≠ packet.take 351 ∧
    load edge.data 228 = 300 ∧ load edge.data 260 = AbiEntry.W - 1 ∧ load edge.data 324 = 0 := by decide +kernel

theorem wrong_base_emitted : EntryTransport.runRejection wrongBase 12 (params .memory) 17
    CanonicalControls.suffix CanonicalControls.machine =
      some (CanonicalControls.machine,some (.revert [])) :=
  EntryTransport.entry_revert_exec wrongBase 12 (params .memory) 17 CanonicalControls.suffix
    CanonicalControls.machine rejected_entries.1 ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩
    (by decide +kernel)

/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.counts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms counts
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.full_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_roundtrip
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.empty_and_fullword' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_and_fullword
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.allocation_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_trace
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.original_input' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms original_input
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.original_verdict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms original_verdict
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.original_values_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms original_values_identity
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.original_layout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms original_layout
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.allocation_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_boundary
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.rejected_entries' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_entries
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.failure_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failure_order
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.changed_accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_accepted
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.byte_controls' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms byte_controls
/-- info: 'Solidity.Backend.AbiWorld.NestedOuterControls.wrong_base_emitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_base_emitted
end Solidity.Backend.AbiWorld.NestedOuterControls
