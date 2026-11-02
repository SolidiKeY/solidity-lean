import Solidity.Backend.AbiWorld.ByteSequenceReadback
import tests.«v13-abi-world».DynamicListControls

/-! Inhabited actual byte-sequence/constructor clients, exact ordered layout
and original zero/header/allocation/fuel/lazy controls. Not runtime encoding. -/
namespace Solidity.Backend.AbiWorld.ByteSequenceControls
open AbiEntry ByteSequenceReadback

def sequence : (bs : List (List UInt8)) → Seq .bytes bs.length
  | [] => .nil
  | b :: bs => .cons (.bytes b) (sequence bs)

theorem tail_sequence (bs : List (List UInt8)) :
    tailBytes (sequence bs) = (bs.map BytesReadback.allocationBytes).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [sequence,tail_cons,ih,List.map_cons,List.sum_cons]

/-- Generic inhabited list-to-existing-Seq client. All actual size/allocation
and original fuel conditions remain explicit; no desired decoding premise. -/
theorem generic_array (bs : List (List UInt8)) (selector post : List UInt8) (free f : Nat) (lazy : Bool)
    (sel : selector.length = 4) (size : (input (.array (sequence bs)) selector post free).size ≤ lim)
    (allocation : free + (bs.length * 32 + 32 + (bs.map BytesReadback.allocationBytes).sum) ≤ lim)
    (fuel : bs.length + 4 ≤ f) :
    ∃ es, entry (input (.array (sequence bs)) selector post free) f (params (.array .bytes) lazy) = .ok es ∧
      bodyValues (input (.array (sequence bs)) selector post free) f (params (.array .bytes) lazy) es 0 =
        .ok (values (.array (sequence bs))) := by
  obtain ⟨es,en,ep,body,run⟩ := array_roundtrip (sequence bs) selector post free f lazy sel size
    (by simpa only [tail_sequence] using allocation) fuel
  exact ⟨es,ep,body⟩

def selector := CanonicalControls.selector
def suffix := CanonicalControls.trailing
def blobs : List (List UInt8) := [[],[0,255],(List.range 33).map UInt8.ofNat]
def xs := sequence blobs

def arrayI : Input := input (.array xs) selector suffix 128
def fixedI : Input := input (.fixed xs) selector suffix 128

theorem cost : tailBytes xs = 192 := by rw [xs,tail_sequence]; decide +kernel

theorem array_typed (lazy : Bool) : ∃ es,
    enter arrayI 7 (params (.array .bytes) lazy) 0 0 = .ok (es,if lazy then 0 else 320) ∧
    entry arrayI 7 (params (.array .bytes) lazy) = .ok es ∧
    bodyValues arrayI 7 (params (.array .bytes) lazy) es 0 = .ok (values (.array xs)) ∧
    verdict arrayI 7 (params (.array .bytes) lazy) = .run (values (.array xs)) := by
  have h := array_roundtrip xs selector suffix 128 7 lazy (by decide +kernel)
    (by rw [array_input_size,cost]; exact (by decide +kernel))
    (by rw [cost]; exact (by decide +kernel)) (by decide +kernel)
  have total : blobs.length * 32 + 32 + tailBytes xs = 320 := by rw [cost]; rfl
  rw [total] at h
  exact h

theorem fixed_typed (lazy : Bool) : ∃ es,
    enter fixedI 7 (params (.fixed .bytes 3) lazy) 0 0 = .ok (es,if lazy then 0 else 288) ∧
    entry fixedI 7 (params (.fixed .bytes 3) lazy) = .ok es ∧
    bodyValues fixedI 7 (params (.fixed .bytes 3) lazy) es 0 = .ok (values (.fixed xs)) ∧
    verdict fixedI 7 (params (.fixed .bytes 3) lazy) = .run (values (.fixed xs)) := by
  have h := fixed_roundtrip xs selector suffix 128 7 lazy (by decide +kernel)
    (by rw [fixed_input_size,cost]; exact (by decide +kernel))
    (by rw [fixed_input_size,cost]; exact (by decide +kernel))
    (by rw [cost]; exact (by decide +kernel)) (by decide +kernel)
  have total : blobs.length * 32 + tailBytes xs = 288 := by rw [cost]; rfl
  rw [total] at h
  exact h

abbrev err := @DynamicListControls.err
def cursor (I : Input) (f : Nat) (ps : List Param) (a : Nat := 0) : Option Nat :=
  DynamicListControls.memoryCursor I f ps a

theorem layout : load arrayI.data 4 = 32 ∧ load arrayI.data 36 = 3 ∧
    load arrayI.data 68 = 96 ∧ load arrayI.data 100 = 128 ∧ load arrayI.data 132 = 192 ∧
    load arrayI.data 164 = 0 ∧ load arrayI.data 196 = 2 ∧ load arrayI.data 260 = 33 ∧
    load fixedI.data 36 = 96 ∧ load fixedI.data 68 = 128 ∧ load fixedI.data 100 = 192 ∧
    cursor arrayI 7 (params (.array .bytes) false) = some 320 ∧
    cursor arrayI 7 (params (.array .bytes) true) = some 0 ∧
    cursor fixedI 7 (params (.fixed .bytes 3) false) = some 288 ∧
    (cref arrayI (.array .bytes) 4 0).toOption = some (68,3) ∧ (cref fixedI (.fixed .bytes 3) 4 0).toOption = some (36,0) := by decide +kernel

def arrayExact : Input := {arrayI with free := lim - 320}
def arrayOver : Input := {arrayExact with free := arrayExact.free + 1}
def fixedExact : Input := {fixedI with free := lim - 288}
def fixedOver : Input := {fixedExact with free := fixedExact.free + 1}
def wrongOffset : Input := ⟨arrayI.data.take 68 ++ AbiEntry.wordBytes (lim + 1) ++ arrayI.data.drop 100,128⟩
def wrongBase : Input := ⟨arrayI.data.take 68 ++ AbiEntry.wordBytes 128 ++ arrayI.data.drop 100,128⟩
def shortHeader : Input := ⟨arrayI.data.take 275,128⟩
def shortPayload : Input := ⟨arrayI.data.take 300,128⟩
def lastAllocPanic : Input := {shortPayload with free := lim - 250}
def headerBeforeAlloc : Input := {shortHeader with free := lim - 250}
def shortHeads : Input := ⟨arrayI.data.take 100,128⟩
def badCount : Input := ⟨selector ++ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes (lim + 1),128⟩
def badOuter : Input := ⟨selector ++ AbiEntry.wordBytes (lim + 1),128⟩

theorem rejected : err (entry wrongOffset 7 (params (.array .bytes) false)) = 1 ∧
    err (entry wrongOffset 0 (params (.array .bytes) false)) = 3 ∧
    err (entry shortHeader 7 (params (.array .bytes) false)) = 1 ∧
    err (entry shortPayload 7 (params (.array .bytes) false)) = 1 ∧
    err (entry badCount 7 (params (.array .bytes) false)) = 2 ∧
    err (entry badCount 7 (params (.array .bytes) true)) = 1 ∧
    err (entry badOuter 7 (params (.array .bytes) false)) = 1 ∧
    err (entry badOuter 0 (params (.array .bytes) false)) = 3 ∧
    err (entry shortHeads 7 (params (.array .bytes) false)) = 1 ∧
    cursor arrayExact 7 (params (.array .bytes) false) = some 320 ∧
    err (entry arrayOver 7 (params (.array .bytes) false)) = 2 ∧
    cursor fixedExact 7 (params (.fixed .bytes 3) false) = some 288 ∧
    err (entry fixedOver 7 (params (.fixed .bytes 3) false)) = 2 := by decide +kernel

theorem priority : err (entry lastAllocPanic 7 (params (.array .bytes) false)) = 2 ∧
    err (entry headerBeforeAlloc 7 (params (.array .bytes) false)) = 1 ∧
    err (entry lastAllocPanic 0 (params (.array .bytes) false)) = 3 ∧
    cursor arrayI 7 (params (.array .bytes) false) 17 = some 337 ∧
    cursor arrayI 7 (params (.array .bytes) false) 17 ≠ some 320 := by decide +kernel

def emptyArray : Input := input (.array (sequence [])) selector [] 128
def emptyFixed : Input := input (.fixed (sequence [])) selector [] 128
def paddedEmptyFixed : Input := input (.fixed (sequence [])) selector (List.replicate 32 0) 128

theorem zero_count : mseq ⟨[],lim + 1⟩ 0 .bytes 999 77 0 17 = .ok (.nil,17) ∧
    err (mdec ⟨[],lim + 1⟩ 1 (.fixed .bytes 0) 0 17) = 1 ∧
    err (mdec ⟨List.replicate 32 0,lim + 1⟩ 1 (.fixed .bytes 0) 0 17) = 2 ∧
    cursor emptyArray 2 (params (.array .bytes) false) = some 32 ∧
    err (entry emptyFixed 2 (params (.fixed .bytes 0) false)) = 1 ∧
    cursor emptyFixed 2 (params (.fixed .bytes 0) true) = some 0 ∧
    cursor paddedEmptyFixed 2 (params (.fixed .bytes 0) false) = some 0 := by
  refine ⟨zero _ _ _ _ _,?_⟩
  decide +kernel

def fixtures : List (List (List UInt8)) :=
  [[],[[]],[[0]],[[255]],[[0,255]],[(List.replicate 31 0),(List.replicate 32 255),(List.range 33).map UInt8.ofNat]]
def fixtureInput (bs : List (List UInt8)) := input (.array (sequence bs)) selector suffix 128

theorem boundaries : fixtures.map (fun bs => (verdict (fixtureInput bs) 8 (params (.array .bytes) false)).kind) =
    List.replicate 6 "run" ∧
    fixtures.map (fun bs => cursor (fixtureInput bs) 8 (params (.array .bytes) false)) =
      [some 32,some 96,some 128,some 128,some 128,some 352] := by decide +kernel

/-- The changed first offset shares the second object's payload. It is
accepted with different ordered values, not silently equated to the original. -/
theorem shared_offset : cursor wrongBase 7 (params (.array .bytes) false) = some 352 ∧
    EntryTransport.bodyObservation wrongBase 7 (params (.array .bytes) false) AbiEntry.encodeArgs =
      some (encodeArgs (values (.array (sequence [[0,255],[0,255],(List.range 33).map UInt8.ofNat])))) ∧
    EntryTransport.bodyObservation wrongBase 7 (params (.array .bytes) false) AbiEntry.encodeArgs ≠
      some (encodeArgs (values (.array xs))) := by decide +kernel

def readonlyZero : List Param := [{shape := .fixed .bytes 0,loc := .calldata,readsOnly := true}]

theorem lazy_zero : (verdict emptyFixed 2 (params (.fixed .bytes 0) true)).kind =
    "blocked: calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics" ∧
    (verdict emptyFixed 2 readonlyZero).kind = "run" ∧
    EntryTransport.bodyObservation emptyFixed 2 readonlyZero AbiEntry.encodeArgs =
      some (encodeArgs (values (.fixed (sequence [])))) := by decide +kernel

def remaining := sequence [[0,255],(List.range 33).map UInt8.ofNat]

/-- Nonzero original sequence index/base and incoming cursor, using actual
windows of the populated input. This is an intrinsic fragment, not a caller
frame or compiled-world provenance claim. -/
theorem reached_fragment : mseq arrayI 4 .bytes 68 1 2 13 = .ok (remaining,173) := by
  have h := sequence_window remaining arrayI (arrayI.data.take 100) (arrayI.data.drop 164)
    (arrayI.data.take 196) suffix 68 1 128 13 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have tail : tailBytes remaining = 160 := by rw [remaining,tail_sequence]; decide +kernel
  simpa only [tail] using h

def shortCount : Input := ⟨arrayI.data.take 50,128⟩
def shortOuter : Input := ⟨arrayI.data.take 20,128⟩

theorem count_and_fuel_priority : err (entry shortCount 7 (params (.array .bytes) false)) = 1 ∧
    err (entry {shortCount with free := lim} 7 (params (.array .bytes) false)) = 1 ∧
    err (entry shortCount 0 (params (.array .bytes) false)) = 3 ∧
    err (entry shortOuter 0 (params (.array .bytes) false)) = 1 ∧
    err (entry arrayI 6 (params (.array .bytes) false)) = 3 ∧
    cursor arrayI 0 (params (.array .bytes) true) = some 0 ∧
    (verdict arrayI 0 (params (.array .bytes) true)).kind = "blocked: ABI decoder fuel exhausted" := by decide +kernel

theorem empty_fixed_typed (lazy : Bool) : ∃ es,
    entry paddedEmptyFixed 4 (params (.fixed .bytes 0) lazy) = .ok es ∧
    bodyValues paddedEmptyFixed 4 (params (.fixed .bytes 0) lazy) es 0 = .ok (values (.fixed (sequence []))) := by
  obtain ⟨es,en,ep,body,run⟩ := fixed_roundtrip (sequence []) selector (List.replicate 32 0) 128 4 lazy
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨es,ep,body⟩


/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.tail_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_sequence
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.generic_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generic_array
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cost
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.array_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_typed
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.fixed_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_typed
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.layout' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms layout
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms rejected
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.priority' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms priority
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.zero_count' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms zero_count
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.boundaries' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms boundaries
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.shared_offset' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms shared_offset
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.lazy_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms lazy_zero
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.reached_fragment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_fragment
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.count_and_fuel_priority' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms count_and_fuel_priority
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceControls.empty_fixed_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_fixed_typed

end Solidity.Backend.AbiWorld.ByteSequenceControls
