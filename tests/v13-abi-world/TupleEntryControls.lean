import Solidity.Backend.AbiWorld.TupleReadback
import tests.«v13-abi-world».BytesEntryControls

/-! Actual generic tuple decoder applications. Codec-only byte comparisons are
separate from classified actual failures. No runtime/native simulation claim. -/
namespace Solidity.Backend.AbiWorld.TupleEntryControls
open AbiEntry TupleReadback

def sel := CanonicalControls.selector
def post := CanonicalControls.trailing
def xs : List UInt := [⟨12,by decide⟩,⟨11,by decide⟩]
def ys : List UInt := [⟨23,by decide⟩,⟨29,by decide⟩]
def wide : List UInt := [⟨0,by decide⟩,⟨300,by decide⟩,MixedPacketControls.edgeScalar]
def marker : UInt := ⟨42,by decide⟩
def bigMarker : UInt := MixedPacketControls.edgeScalar
def pair := pairInput xs ys sel post 128
def mixed := mixedInput xs marker sel post 128

theorem pairs (l r : Bool) :
    enter pair 6 (pairParams l r) 0 0 = .ok (pairEntries l r xs ys,spent l xs + spent r ys) ∧
    verdict pair 6 (pairParams l r) = .run (ArrayPairPacket.values xs ys) :=
  pair_entry xs ys sel post 128 6 l r (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem mixed_roundtrip (l : Bool) :
    verdict mixed 6 (mixedLocations l) = .run (MixedPacket.values xs marker) ∧
    verdict (reverseInput xs marker sel post 128) 6 (reverseParams l) = .run (reverseValues xs marker) :=
  ⟨(mixed_locations xs marker sel post 128 6 l (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2,
   (reverse_entry xs marker sel post 128 6 l (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2⟩

/-- Equal contents do not require disjoint references. These are codec/input
fixtures, not an assertion that two allocations in this decoder alias. -/
theorem equal_arrays (l r : Bool) : verdict (pairInput xs xs sel post 128) 6 (pairParams l r) =
    .run (ArrayPairPacket.values xs xs) :=
  (pair_entry xs xs sel post 128 6 l r (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem empty_pair (l r : Bool) : verdict (pairInput [] [] sel post 128) 4 (pairParams l r) =
    .run (ArrayPairPacket.values [] []) :=
  (pair_entry [] [] sel post 128 4 l r (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem full_words (l r : Bool) :
    verdict (pairInput wide [] sel post 128) 7 (pairParams l r) = .run (ArrayPairPacket.values wide []) ∧
    verdict (mixedInput wide bigMarker sel post 128) 7 (mixedLocations l) = .run (MixedPacket.values wide bigMarker) ∧
    verdict (reverseInput [] bigMarker sel post 128) 4 (reverseParams l) = .run (reverseValues [] bigMarker) :=
  ⟨(pair_entry wide [] sel post 128 7 l r (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).2,
   (mixed_locations wide bigMarker sel post 128 7 l (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).2,
   (reverse_entry [] bigMarker sel post 128 4 l (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).2⟩

def boundary := pairInput xs ys sel post (lim - 192)
def oneOver := pairInput xs ys sel post (lim - 191)

theorem cursor_boundary : enter boundary 6 (pairParams false false) 0 0 =
    .ok (pairEntries false false xs ys,192) ∧ verdict boundary 6 (pairParams false false) =
    .run (ArrayPairPacket.values xs ys) := by
  exact pair_entry xs ys sel post (lim - 192) 6 false false (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Complete codec bytes as observed by the actual body after decoding. -/
theorem observed (l r : Bool) : EntryTransport.bodyObservation pair 6 (pairParams l r) encodeArgs =
    some (encodeArgs (ArrayPairPacket.values xs ys)) := by
  unfold EntryTransport.bodyObservation
  rw [(pairs l r).2]

private theorem failed {ε α : Type} (x : Except ε α) (e : ε)
    (h : (match x with | .error a => some a | .ok _ => none) = some e) : x = .error e := by
  cases x with
  | error a => cases h; rfl
  | ok a => cases h

def wrongOffset : Input := ⟨sel ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 4096 ++
  ArrayPairPacket.payload xs ++ ArrayPairPacket.payload ys,128⟩
def missingHead : Input := ⟨sel ++ AbiEntry.wordBytes 64,128⟩
def shortTail : Input := ⟨(sel ++ encodeArgs (ArrayPairPacket.values xs ys)).take 259,128⟩
def firstTight : Input := ⟨wrongOffset.data,lim - 95⟩
def secondTight : Input := ⟨shortTail.data,lim - 191⟩

theorem failed_entries : entry oneOver 6 (pairParams false false) = .error .panic ∧
    entry wrongOffset 6 (pairParams false false) = .error .revert ∧
    entry missingHead 6 (pairParams false false) = .error .revert ∧
    entry shortTail 6 (pairParams false false) = .error .revert ∧
    entry pair 5 (pairParams false false) = .error .fuel := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),
    failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

/-- Ordered real failure priority: allocation in the first parameter precedes
an invalid second offset; second allocation precedes its truncated payload. -/
theorem failure_priority : entry firstTight 6 (pairParams false false) = .error .panic ∧
    entry secondTight 6 (pairParams false false) = .error .panic ∧
    (verdict oneOver 6 (pairParams false false)).kind = "blocked: possible Panic(0x41) allocation failure in memory decoding" ∧
    (verdict pair 5 (pairParams false false)).kind = "blocked: ABI decoder fuel exhausted" ∧
    (verdict shortTail 6 (pairParams true true)).kind = "revert" := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),
    by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- Wrong-byte equalities are not classified decoder failures. Swapped and
stale packets can themselves be valid canonical inputs for other values. -/
theorem byte_negatives :
    encodeArgs (ArrayPairPacket.values xs ys) ≠ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 64 ++
      ArrayPairPacket.payload xs ++ ArrayPairPacket.payload ys ∧
    encodeArgs (ArrayPairPacket.values xs ys) ≠ encodeArgs (ArrayPairPacket.values ys xs) ∧
    encodeArgs (MixedPacket.values xs marker) ≠ encodeArgs (reverseValues xs marker) ∧
    encodeArgs (MixedPacket.values xs marker) ≠ encodeArgs (MixedPacket.values xs bigMarker) := by decide +kernel

theorem swapped_valid (l r : Bool) : verdict (pairInput ys xs sel post 128) 6 (pairParams l r) =
    .run (ArrayPairPacket.values ys xs) :=
  (pair_entry ys xs sel post 128 6 l r (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2


/-- The summed generic premise is only sufficient: calldata body copies start
at cursor zero separately in the existing bodyValues definition. -/
theorem lazy_capacity : (verdict (pairInput xs ys sel post (lim - 96)) 6 (pairParams true true)).kind = "run" ∧
    spent false xs + spent false ys = 192 ∧ spent false xs + spent true ys = 96 ∧
    spent true xs + spent false ys = 96 ∧ spent true xs + spent true ys = 0 := by decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.pairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairs
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.mixed_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_roundtrip
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.equal_arrays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms equal_arrays
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.empty_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_pair
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.full_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_words
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.cursor_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cursor_boundary
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.observed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observed
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.failed_entries' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms failed_entries
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.failure_priority' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms failure_priority
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.byte_negatives' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms byte_negatives
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.swapped_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms swapped_valid
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.lazy_capacity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms lazy_capacity


def stale : List UInt := [⟨7,by decide⟩,⟨11,by decide⟩]

theorem stale_valid : verdict (pairInput stale ys sel post 128) 6 (pairParams false true) =
    .run (ArrayPairPacket.values stale ys) ∧ encodeArgs (ArrayPairPacket.values stale ys) ≠
    encodeArgs (ArrayPairPacket.values xs ys) :=
  ⟨(pair_entry stale ys sel post 128 6 false true (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2,by decide +kernel⟩

theorem mixed_boundary : verdict (mixedInput xs marker sel post (lim - 96)) 6 (mixedLocations false) =
    .run (MixedPacket.values xs marker) ∧
    entry (mixedInput xs marker sel post (lim - 95)) 6 (mixedLocations false) = .error .panic :=
  ⟨(mixed_locations xs marker sel post (lim - 96) 6 false (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2,failed _ _ (by decide +kernel)⟩

/-- Arbitrary selector/trailing values are not compared to a hardcoded selector. -/
theorem different_selector : verdict (mixedInput [] bigMarker [0,1,2,255] [255,0,14] 32) 4
    (mixedLocations true) = .run (MixedPacket.values [] bigMarker) :=
  (mixed_locations [] bigMarker [0,1,2,255] [255,0,14] 32 4 true (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.stale_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_valid
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.mixed_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_boundary
/-- info: 'Solidity.Backend.AbiWorld.TupleEntryControls.different_selector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms different_selector
end Solidity.Backend.AbiWorld.TupleEntryControls
