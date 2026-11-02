import Solidity.Backend.AbiWorld.TripleReadback
import tests.«v13-abi-world».BytesArrayControls

/-! Actual typed triple admission and ordered BODY failures. These controls
use actual calldata entry origins and preserve the earlier finite observation.
No source/native/runtime-return/world relation is asserted. -/
namespace Solidity.Backend.AbiWorld.BodyTripleControls
open AbiEntry TripleReadback

def bs := BytesArrayControls.bs
def xs := BytesArrayControls.xs
def marker := TupleEntryControls.marker
def sel := CanonicalControls.selector
def post := CanonicalControls.trailing
def sample := input bs xs marker sel post 128

theorem typed (bl al : Bool) : enter sample 5 (params bl al) 0 0 = .ok (entries bl al bs xs marker,cursor bl al bs xs) ∧
    entry sample 5 (params bl al) = .ok (entries bl al bs xs marker) ∧
    bodyValues sample 5 (params bl al) (entries bl al bs xs marker) 0 = .ok (values bs xs marker) ∧
    verdict sample 5 (params bl al) = .run (values bs xs marker) :=
  roundtrip bs xs marker sel post 128 5 bl al (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem old_values : values bs xs marker = BytesArrayControls.tripleValues := rfl

theorem old_input : sample = BytesArrayControls.triple := by
  unfold sample input BytesArrayControls.triple
  rw [old_values]
  rfl

/-- Strengthens the EXACT retained old fixture to generic typed entry/body
identity, without modifying its packet or its original finite observation. -/
theorem old_typed : entry BytesArrayControls.triple 5 BytesArrayControls.tripleParams =
    .ok (entries false false bs xs marker) ∧ bodyValues BytesArrayControls.triple 5 BytesArrayControls.tripleParams
      (entries false false bs xs marker) 0 = .ok BytesArrayControls.tripleValues := by
  have h := typed false false
  rw [old_input,old_values] at h
  exact ⟨h.2.1,h.2.2.1⟩

theorem family (bl al : Bool) : ∀ b ∈ [[],BytesEntryControls.b31,BytesEntryControls.b32,BytesEntryControls.b33],
    verdict (input b xs marker sel post 128) 5 (params bl al) = .run (values b xs marker) := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  all_goals exact (roundtrip _ xs marker sel post 128 5 bl al (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2.2.2

theorem empty_full (bl al : Bool) : verdict (input [] [] TupleEntryControls.bigMarker sel post 128) 4 (params bl al) =
    .run (values [] [] TupleEntryControls.bigMarker) ∧
    verdict (input [0,255] TupleEntryControls.wide TupleEntryControls.bigMarker [0,1,2,255] [255,0,14] 128) 7 (params bl al) =
    .run (values [0,255] TupleEntryControls.wide TupleEntryControls.bigMarker) :=
  ⟨(roundtrip [] [] TupleEntryControls.bigMarker sel post 128 4 bl al (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).2.2.2,
   (roundtrip [0,255] TupleEntryControls.wide TupleEntryControls.bigMarker [0,1,2,255] [255,0,14] 128 7 bl al
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2.2.2⟩

theorem references : load sample.data 4 = 96 ∧ load sample.data 36 = 192 ∧ load sample.data 68 = 42 ∧
    (match cref sample .bytes 4 0 with | .ok v => some v | .error _ => none) = some (132,33) ∧
    (match cref sample WordArrayPacket.Shape 4 32 with | .ok v => some v | .error _ => none) = some (228,1) ∧
    cursor false false bs xs = 160 ∧ cursor false true bs xs = 96 ∧ cursor true false bs xs = 64 ∧ cursor true true bs xs = 0 := by decide +kernel

def boundary := input bs xs marker sel post (lim - 160)
def oneOver := input bs xs marker sel post (lim - 159)
def tight := input bs xs marker sel post (lim - 95)
def wrongOffset : Input := ⟨sel ++ AbiEntry.wordBytes 96 ++ AbiEntry.wordBytes 4096 ++ AbiEntry.wordBytes 42 ++
  BytesArrayReadback.bytePayload bs ++ BytesArrayReadback.arrayPayload xs,128⟩
def prefixTight : Input := ⟨wrongOffset.data,lim - 95⟩
def shortArray : Input := ⟨(sel ++ encodeArgs (values bs xs marker)).take 259,128⟩
def shortHeader : Input := ⟨sel ++ AbiEntry.wordBytes 96 ++ AbiEntry.wordBytes 192 ++ AbiEntry.wordBytes 42 ++
  (AbiEntry.wordBytes 33).take 31,lim - 31⟩
def missingHead : Input := ⟨sel ++ AbiEntry.wordBytes 96 ++ AbiEntry.wordBytes 192,lim⟩

private theorem failed {ε α : Type} (x : Except ε α) (e : ε)
    (h : (match x with | .error a => some a | .ok _ => none) = some e) : x = .error e := by
  cases x with
  | error a => cases h; rfl
  | ok a => cases h

theorem allocation_limit : verdict boundary 5 (params false false) = .run (values bs xs marker) :=
  (roundtrip bs xs marker sel post (lim - 160) 5 false false (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2.2.2

theorem entry_failures : entry oneOver 5 (params false false) = .error .panic ∧
    entry wrongOffset 5 (params false false) = .error .revert ∧ entry prefixTight 5 (params false false) = .error .panic ∧
    entry shortArray 5 (params false false) = .error .revert ∧ entry shortHeader 5 (params false false) = .error .revert ∧
    entry missingHead 5 (params false false) = .error .revert := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),
    failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

def byteEs : Entries [BytesArrayReadback.byteParam true] := .cons (BytesArrayReadback.byteEntry true bs 96) .nil
def tailEs : Entries [TupleReadback.arrayParam true,TupleReadback.scalarParam] :=
  .cons (TupleReadback.arrayEntry true xs 192) (tailEntries marker)
def lazyError := "calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics"
def fuelError := "ABI decoder fuel exhausted"

/-- Actual entry succeeds even at the body-failure cases: this is not a
well-typed invented frame mistaken for an entered caller body. -/
theorem calldata_origins : entry sample 2 (params true true) = .ok (entries true true bs xs marker) ∧
    entry tight 2 (params true true) = .ok (entries true true bs xs marker) :=
  ⟨calldata_entry bs xs marker sel post 128 2 (by decide +kernel) (by decide +kernel) (by decide +kernel),
   calldata_entry bs xs marker sel post (lim - 95) 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem prefix_positive : bodyValues sample 2 [BytesArrayReadback.byteParam true] byteEs 0 = .ok (.cons (.bytes bs) .nil) :=
  bytes_prefix bs xs marker sel post 128 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tail_fuel : bodyValues sample 2 [TupleReadback.arrayParam true,TupleReadback.scalarParam] tailEs 32 = .error fuelError ∧
    bodyValues tight 2 [TupleReadback.arrayParam true,TupleReadback.scalarParam] tailEs 32 = .error fuelError :=
  ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

/-- Successful actual prefix, then tail fuel: consumes generic typed body composition. -/
theorem composed_tail_failure : bodyValues sample 2 (params true true) (entries true true bs xs marker) 0 = .error fuelError := by
  exact BodyComposition.body_tail_failure sample 2 byteEs tailEs (.cons (.bytes bs) .nil) 0 fuelError
    prefix_positive tail_fuel.1

/-- Allocation/lazy refusal in first body parameter precedes the independently
failing tail's fuel error, with both frames coming from actual calldata entry. -/
theorem composed_prefix_failure : bodyValues tight 2 (params true true) (entries true true bs xs marker) 0 = .error lazyError := by
  have h : bodyValues tight 2 [BytesArrayReadback.byteParam true] byteEs 0 = .error lazyError := failed _ _ (by decide +kernel)
  exact BodyComposition.body_prefix_failure tight 2 byteEs tailEs 0 lazyError h

theorem failure_classifications : (verdict sample 2 (params true true)).kind = "blocked: ABI decoder fuel exhausted" ∧
    (verdict tight 2 (params true true)).kind = "blocked: " ++ lazyError := by decide +kernel

/-- The correct reached allocation cursor is96; a one-byte cursor error at
exact capacity produces an actual allocator Panic. No physical-world claim. -/
theorem cursor_positive : melem boundary 5 WordArrayPacket.Shape 4 36 96 =
    .ok (.array (WordArrayPacket.sequence xs),160) :=
  TupleReadback.array_window xs boundary 32 192 96 5 post (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem wrong_cursor : melem boundary 5 WordArrayPacket.Shape 4 36 97 = .error .panic := failed _ _ (by decide +kernel)

theorem wrong_head_and_bytes :
    (match bodyValues sample 5 [TupleReadback.arrayParam true,TupleReadback.scalarParam] tailEs 32 with
      | .ok vs => some (encodeArgs vs) | .error _ => none) = some (encodeArgs (MixedPacket.values xs marker)) ∧
    bodyValues sample 5 [TupleReadback.arrayParam true,TupleReadback.scalarParam] tailEs 64 = .error lazyError ∧
    encodeArgs (values bs xs marker) ≠ encodeArgs (BytesArrayReadback.values bs xs) ∧
    encodeArgs (values bs xs marker) ≠ encodeArgs (values bs xs TupleEntryControls.bigMarker) := by
  exact ⟨by decide +kernel,failed _ _ (by decide +kernel),by decide +kernel,by decide +kernel⟩


/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.old_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms old_values
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.old_input' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms old_input
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.old_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms old_typed
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms family
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.empty_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_full
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.references' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms references
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.allocation_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_limit
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.entry_failures' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms entry_failures
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.calldata_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_origins
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.prefix_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_positive
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.tail_fuel' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tail_fuel
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.composed_tail_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composed_tail_failure
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.composed_prefix_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms composed_prefix_failure
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.failure_classifications' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms failure_classifications
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.cursor_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cursor_positive
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.wrong_cursor' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_cursor
/-- info: 'Solidity.Backend.AbiWorld.BodyTripleControls.wrong_head_and_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_head_and_bytes
end Solidity.Backend.AbiWorld.BodyTripleControls
