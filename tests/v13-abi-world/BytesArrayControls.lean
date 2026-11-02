import Solidity.Backend.AbiWorld.BytesArrayReadback
import tests.«v13-abi-world».TupleEntryControls

/-! Actual heterogeneous dynamic readback and structural composition controls.
No runtime/native encoder, source/world frame or admitted-profile closure. -/
namespace Solidity.Backend.AbiWorld.BytesArrayControls
open AbiEntry BytesArrayReadback

def sel := CanonicalControls.selector
def post := CanonicalControls.trailing
def bs := BytesEntryControls.b33
def xs : List UInt := [⟨300,by decide⟩]
def wide := TupleEntryControls.wide
def sample := input bs xs sel post 128
def reversed := reverseInput bs xs sel post 128

theorem roundtrip (bl al : Bool) :
    enter sample 5 (params bl al) 0 0 = .ok (entries bl al bs xs,spentBytes bl bs + TupleReadback.spent al xs) ∧
    verdict sample 5 (params bl al) = .run (values bs xs) ∧
    enter reversed 5 (reverseParams bl al) 0 0 =
      .ok (reverseEntries bl al bs xs,TupleReadback.spent al xs + spentBytes bl bs) ∧
    verdict reversed 5 (reverseParams bl al) = .run (reverseValues bs xs) := by
  have a := entry_body bs xs sel post 128 5 bl al (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have b := reverse_entry_body bs xs sel post 128 5 bl al (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  exact ⟨a.1,a.2,b.1,b.2⟩

theorem empty (bl al : Bool) : verdict (input [] [] sel post 128) 4 (params bl al) = .run (values [] []) ∧
    verdict (reverseInput [] [] sel post 128) 4 (reverseParams bl al) = .run (reverseValues [] []) :=
  ⟨(entry_body [] [] sel post 128 4 bl al (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2,
   (reverse_entry_body [] [] sel post 128 4 bl al (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2⟩

theorem full_words (bl al : Bool) : verdict (input [0,255] wide sel post 128) 7 (params bl al) =
    .run (values [0,255] wide) ∧ verdict (reverseInput [0,255] wide sel post 128) 7 (reverseParams bl al) =
    .run (reverseValues [0,255] wide) :=
  ⟨(entry_body [0,255] wide sel post 128 7 bl al (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2,
   (reverse_entry_body [0,255] wide sel post 128 7 bl al (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2⟩

theorem boundaries (bl al : Bool) : ∀ b ∈ [BytesEntryControls.b31,BytesEntryControls.b32,BytesEntryControls.b33],
    verdict (input b xs sel post 128) 5 (params bl al) = .run (values b xs) ∧
    verdict (reverseInput b xs sel post 128) 5 (reverseParams bl al) = .run (reverseValues b xs) := by
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  all_goals exact ⟨(entry_body _ xs sel post 128 5 bl al (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2,
   (reverse_entry_body _ xs sel post 128 5 bl al (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2⟩

private theorem succeeded {ε α : Type} (x : Except ε α) (a : α)
    (h : (match x with | .ok v => some v | .error _ => none) = some a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok v => cases h; rfl

/-- Unequal byte/array costs distinguish order, heads, pointers and cursors. -/
theorem offsets_cursors : load sample.data 4 = 64 ∧ load sample.data 36 = 160 ∧
    load reversed.data 4 = 64 ∧ load reversed.data 36 = 128 ∧
    cref sample .bytes 4 0 = .ok (100,33) ∧ cref sample WordArrayPacket.Shape 4 32 = .ok (196,1) ∧
    cref reversed WordArrayPacket.Shape 4 0 = .ok (100,1) ∧ cref reversed .bytes 4 32 = .ok (164,33) ∧
    spentBytes false bs + TupleReadback.spent false xs = 160 ∧
    spentBytes false bs + TupleReadback.spent true xs = 96 ∧
    spentBytes true bs + TupleReadback.spent false xs = 64 ∧
    spentBytes true bs + TupleReadback.spent true xs = 0 := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    succeeded _ _ (by decide +kernel),succeeded _ _ (by decide +kernel),
    succeeded _ _ (by decide +kernel),succeeded _ _ (by decide +kernel),
    by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

def boundary :=  input bs xs sel post (lim - 160)
def oneOver := input bs xs sel post (lim - 159)
def reverseExact := reverseInput bs xs sel post (lim - 160)
def reverseOneOver := reverseInput bs xs sel post (lim - 159)

theorem allocation_limit : verdict boundary 5 (params false false) = .run (values bs xs) ∧
    verdict reverseExact 5 (reverseParams false false) = .run (reverseValues bs xs) :=
  ⟨(entry_body bs xs sel post (lim - 160) 5 false false (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2,
   (reverse_entry_body bs xs sel post (lim - 160) 5 false false (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2⟩

private theorem failed {ε α : Type} (x : Except ε α) (e : ε)
    (h : (match x with | .error a => some a | .ok _ => none) = some e) : x = .error e := by
  cases x with
  | error a => cases h; rfl
  | ok a => cases h

def farSecond : Input := ⟨sel ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 4096 ++ bytePayload bs ++ arrayPayload xs,128⟩
def reverseFarSecond : Input := ⟨sel ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 4096 ++ arrayPayload xs ++ bytePayload bs,128⟩
def prefixTight : Input := ⟨farSecond.data,lim - 95⟩
def reversePrefixTight : Input := ⟨reverseFarSecond.data,lim - 63⟩
def shortArray : Input := ⟨(sel ++ encodeArgs (values bs xs)).take 227,128⟩
def shortBytes : Input := ⟨(sel ++ encodeArgs (reverseValues bs xs)).take 196,128⟩
def shortBytesTight : Input := ⟨shortBytes.data,lim - 159⟩
def shortHeader : Input := ⟨sel ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 160 ++ (AbiEntry.wordBytes 33).take 31,lim - 31⟩
def missingHead : Input := ⟨sel ++ AbiEntry.wordBytes 64,lim⟩

theorem failures : entry oneOver 5 (params false false) = .error .panic ∧
    entry reverseOneOver 5 (reverseParams false false) = .error .panic ∧
    entry farSecond 5 (params false false) = .error .revert ∧
    entry reverseFarSecond 5 (reverseParams false false) = .error .revert ∧
    entry shortArray 5 (params false false) = .error .revert ∧
    entry shortBytes 5 (reverseParams false false) = .error .revert ∧
    entry shortHeader 5 (params false false) = .error .revert ∧
    entry missingHead 5 (params false false) = .error .revert := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),
    failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),
    failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

theorem priority : entry prefixTight 5 (params false false) = .error .panic ∧
    entry reversePrefixTight 5 (reverseParams false false) = .error .panic ∧
    entry shortBytesTight 5 (reverseParams false false) = .error .panic := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

/-- A real checked prefix failure consumes the unconditional composition law. -/
theorem prefix_transport : enter prefixTight 5 ([byteParam false] ++ [TupleReadback.arrayParam false]) 0 0 = .error .panic :=
  EntryComposition.prefix_failure prefixTight 5 [byteParam false] [TupleReadback.arrayParam false] 0 0 .panic
    (failed _ _ (by decide +kernel))

theorem classifications : (verdict oneOver 5 (params false false)).kind =
    "blocked: possible Panic(0x41) allocation failure in memory decoding" ∧
    (verdict sample 0 (params true true)).kind = "blocked: ABI decoder fuel exhausted" ∧
    (match entry sample 0 (params true true) with | .ok _ => true | .error _ => false) = true ∧
    (verdict (input bs xs sel post (lim - 96)) 5 (params true true)).kind = "run" ∧
    (verdict (input bs xs sel post (lim - 95)) 5 (params true true)).kind =
      "blocked: calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics" := by decide +kernel

/-- Positive reversed identities above precede byte-order negatives. Equal
word/byte content is not typed equality or an assertion of heap aliasing. -/
theorem negative_bytes : encodeArgs (values bs xs) ≠ encodeArgs (reverseValues bs xs) ∧
    encodeArgs (values bs xs) ≠ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 128 ++ bytePayload bs ++ arrayPayload xs ∧
    encodeArgs (reverseValues bs xs) ≠ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes 160 ++ arrayPayload xs ++ bytePayload bs ∧
    encodeArgs (values [0] []) ≠ encodeArgs (values [] []) ∧
    encodeArgs (values [255] [⟨300,by decide⟩]) ≠ encodeArgs (values [255] [⟨44,by decide⟩]) := by decide +kernel

def tripleValues : Vals [.bytes,WordArrayPacket.Shape,MixedPacket.ScalarShape] :=
  ArrayPairPacket.append (values bs xs) (.cons (.word (WordArrayPacket.uintWord TupleEntryControls.marker)) .nil)
def tripleParams : List Param := params false false ++ [TupleReadback.scalarParam]
def triple : Input := ⟨sel ++ encodeArgs tripleValues ++ post,128⟩

/-- Finite actual three-parameter decoder/control; not a generic triple theorem. -/
theorem triple_observed : EntryTransport.bodyObservation triple 5 tripleParams encodeArgs = some (encodeArgs tripleValues) ∧
    load triple.data 4 = 96 ∧ load triple.data 36 = 192 ∧ load triple.data 68 = 42 := by decide +kernel


/-- Full padding remains part of the canonical codec but is not an entry
content validator. Both actual orders preserve complete body normalization. -/
theorem padding : ((encodeArgs (values bs xs)).drop 129).take 31 = List.replicate 31 0 ∧
    ((encodeArgs (reverseValues bs xs)).drop 193).take 31 = List.replicate 31 0 ∧
    (encodeArgs (values BytesEntryControls.b31 xs)).length = 192 ∧
    (encodeArgs (values BytesEntryControls.b32 xs)).length = 192 ∧
    (encodeArgs (values bs xs)).length = 224 := by decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundtrip
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.full_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_words
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundaries
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.offsets_cursors' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms offsets_cursors
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.allocation_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_limit
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.failures' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms failures
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.priority' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms priority
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.prefix_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_transport
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.classifications' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms classifications
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.negative_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms negative_bytes
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.triple_observed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms triple_observed
/-- info: 'Solidity.Backend.AbiWorld.BytesArrayControls.padding' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms padding
end Solidity.Backend.AbiWorld.BytesArrayControls
