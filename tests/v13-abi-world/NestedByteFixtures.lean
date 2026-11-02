import Solidity.Backend.AbiWorld.NestedByteListReadback
import tests.«v13-abi-world».ByteSequenceControls

/-! Inhabited recursive byte-array and heterogeneous clients. Finite pure
observations are distinct from the generic kernel proofs and target machines. -/
namespace Solidity.Backend.AbiWorld.NestedByteControls
open AbiEntry NestedByteReadback
open ByteSequenceReadback (input params values)

def sequence : (bs : List (List (List UInt8))) → Seq Element bs.length
  | [] => .nil
  | b :: bs => .cons (.array (ByteSequenceControls.sequence b)) (sequence bs)

theorem tail_sequence (bs : List (List (List UInt8))) :
    tailCost (sequence bs) = (bs.map (fun b => innerCost (ByteSequenceControls.sequence b))).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [sequence,tail_cons,ih,List.map_cons,List.sum_cons]

/-- Inhabited arbitrary outer/inner counts, actual existing Seq constructors
and explicit original sufficient input/allocation/fuel bounds. -/
theorem generic_array (bs : List (List (List UInt8))) (sel post : List UInt8) (free f : Nat) (lazy : Bool)
    (selector : sel.length = 4) (size : (input (.array (sequence bs)) sel post free).size ≤ lim)
    (allocation : free + (bs.length * 32 + 32 + tailCost (sequence bs)) ≤ lim)
    (fuel : fuelNeed (sequence bs) + 2 ≤ f) :
    ∃ es, entry (input (.array (sequence bs)) sel post free) f (params (.array Element) lazy) = .ok es ∧
      bodyValues (input (.array (sequence bs)) sel post free) f (params (.array Element) lazy) es 0 =
        .ok (values (.array (sequence bs))) := by
  obtain ⟨es,en,ep,body,run⟩ := array_roundtrip (sequence bs) sel post free f lazy selector size allocation fuel
  exact ⟨es,ep,body⟩

def selector := CanonicalControls.selector
def suffix := CanonicalControls.trailing
def blobs : List (List (List UInt8)) := [[],[[],[0,255]],[(List.range 33).map UInt8.ofNat]]
def xs := sequence blobs

theorem cost : tailCost xs = 384 := by
  rw [xs,tail_sequence]
  simp only [blobs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,innerCost,
    ByteSequenceControls.tail_sequence,List.length_cons,List.length_nil]
  decide +kernel

theorem fuel_bound : fuelNeed xs = 8 := by decide +kernel

def arrayI : Input := input (.array xs) selector suffix 128
def fixedI : Input := input (.fixed xs) selector suffix 128
def mixedI : Input := NestedByteListReadback.input xs UniformWordControls.big selector suffix 128

theorem array_typed (lazy : Bool) : ∃ es,
    enter arrayI 10 (params (.array Element) lazy) 0 0 = .ok (es,if lazy then 0 else 512) ∧
    entry arrayI 10 (params (.array Element) lazy) = .ok es ∧
    bodyValues arrayI 10 (params (.array Element) lazy) es 0 = .ok (values (.array xs)) ∧
    verdict arrayI 10 (params (.array Element) lazy) = .run (values (.array xs)) := by
  have h := array_roundtrip xs selector suffix 128 10 lazy (by decide +kernel)
    (by rw [array_input_size,cost]; exact (by decide +kernel))
    (by rw [cost]; exact (by decide +kernel)) (by rw [fuel_bound]; decide +kernel)
  have total : blobs.length * 32 + 32 + tailCost xs = 512 := by rw [cost]; rfl
  rw [total] at h
  exact h

theorem fixed_typed (lazy : Bool) : ∃ es,
    enter fixedI 10 (params (.fixed Element 3) lazy) 0 0 = .ok (es,if lazy then 0 else 480) ∧
    entry fixedI 10 (params (.fixed Element 3) lazy) = .ok es ∧
    bodyValues fixedI 10 (params (.fixed Element 3) lazy) es 0 = .ok (values (.fixed xs)) ∧
    verdict fixedI 10 (params (.fixed Element 3) lazy) = .run (values (.fixed xs)) := by
  have h := fixed_roundtrip xs selector suffix 128 10 lazy (by decide +kernel)
    (by rw [fixed_input_size,cost]; exact (by decide +kernel))
    (by rw [fixed_input_size,cost]; exact (by decide +kernel))
    (by rw [cost]; exact (by decide +kernel)) (by rw [fuel_bound]; decide +kernel)
  have total : blobs.length * 32 + tailCost xs = 480 := by rw [cost]; rfl
  rw [total] at h
  exact h

theorem mixed_typed (lazy : Bool) : ∃ es,
    enter mixedI 10 (NestedByteListReadback.params (.uint 256) lazy) 0 0 = .ok (es,if lazy then 0 else 512) ∧
    entry mixedI 10 (NestedByteListReadback.params (.uint 256) lazy) = .ok es ∧
    bodyValues mixedI 10 (NestedByteListReadback.params (.uint 256) lazy) es 0 =
      .ok (NestedByteListReadback.packet xs UniformWordControls.big) ∧
    verdict mixedI 10 (NestedByteListReadback.params (.uint 256) lazy) =
      .run (NestedByteListReadback.packet xs UniformWordControls.big) := by
  have h := NestedByteListReadback.roundtrip xs UniformWordControls.big selector suffix 128 10 lazy (by decide +kernel)
    (by rw [NestedByteListReadback.input_size,cost]; exact (by decide +kernel))
    (by rw [cost]; exact (by decide +kernel)) (by rw [fuel_bound]; decide +kernel)
  have total : blobs.length * 32 + 32 + tailCost xs = 512 := by rw [cost]; rfl
  rw [total] at h
  exact h

abbrev err := @DynamicListControls.err
def cursor (I : Input) (f : Nat) (ps : List Param) (a : Nat := 0) : Option Nat :=
  DynamicListControls.memoryCursor I f ps a

def exactArray : Input := {arrayI with free := lim - 512}
def overArray : Input := {exactArray with free := exactArray.free + 1}
def exactFixed : Input := {fixedI with free := lim - 480}
def overFixed : Input := {exactFixed with free := exactFixed.free + 1}
def wrongBase : Input := ⟨arrayI.data.take 68 ++ AbiEntry.wordBytes 64 ++ arrayI.data.drop 100,128⟩
def badOffset : Input := ⟨arrayI.data.take 68 ++ AbiEntry.wordBytes (lim + 1) ++ arrayI.data.drop 100,128⟩
def badCount : Input := ⟨selector ++ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes (lim + 1),128⟩
def badInnerCount : Input := ⟨arrayI.data.take 388 ++ AbiEntry.wordBytes (lim + 1) ++ arrayI.data.drop 420,128⟩
def shortCount : Input := ⟨arrayI.data.take 50,128⟩
def shortOuter : Input := ⟨arrayI.data.take 20,128⟩
def shortInnerCount : Input := ⟨arrayI.data.take 400,128⟩
def shortPayload : Input := ⟨arrayI.data.take 500,128⟩
def lastPanic : Input := {shortPayload with free := lim - 450}
def shortHeader : Input := ⟨arrayI.data.take 460,lim - 450⟩

def sharedOuter : Input := ⟨arrayI.data.take 68 ++ AbiEntry.wordBytes 128 ++ arrayI.data.drop 100,128⟩
def sharedInner : Input := ⟨arrayI.data.take 228 ++ AbiEntry.wordBytes 96 ++ arrayI.data.drop 260,128⟩

def fixtures : List (List (List (List UInt8))) :=
  [[],[[]],[[[]]],[[[0]],[[255]]],[[List.replicate 31 0,List.replicate 32 255,(List.range 33).map UInt8.ofNat]],blobs]
def fixtureInput (bs : List (List (List UInt8))) := input (.array (sequence bs)) selector suffix 128

def emptyFixed : Input := input (.fixed (sequence [])) selector [] 128
def paddedEmptyFixed : Input := input (.fixed (sequence [])) selector (List.replicate 32 0) 128
def readonlyZero : List Param := [{shape := .fixed Element 0,loc := .calldata,readsOnly := true}]



/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.tail_sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_sequence
/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.generic_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generic_array
/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cost
/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.fuel_bound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fuel_bound
/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.array_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_typed
/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.fixed_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_typed
/-- info: 'Solidity.Backend.AbiWorld.NestedByteControls.mixed_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_typed

end Solidity.Backend.AbiWorld.NestedByteControls
