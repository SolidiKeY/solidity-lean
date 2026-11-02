import Solidity.Backend.AbiWorld.StaticAggregateReadback
import tests.«v13-abi-world».BodyTripleControls

/-! Inhabited arbitrary-length validated word-list and actual tuple/fixed
constructor controls. Intrinsic location/empty-constructor cases do not add
Source admission or unknown-memory runtime encoding. -/
namespace Solidity.Backend.AbiWorld.UniformWordControls
open AbiEntry WordListReadback StaticAggregateReadback

def sel := CanonicalControls.selector
def post := CanonicalControls.trailing
def u8 : Word (.uint 8) := ⟨255,by decide +kernel,by decide +kernel⟩
def b1 : Word .bool := ⟨1,by decide +kernel,by decide +kernel⟩
def en : Word (.enumBelow 3) := ⟨2,by decide +kernel,by decide +kernel⟩
def neg : Word (.int 8) := ⟨AbiEntry.W - 1,by decide +kernel,by decide +kernel⟩
def fb : Word (.fixedBytes 32) := ⟨300,by decide +kernel,by decide +kernel⟩
def big : Word (.uint 256) := WordArrayPacket.uintWord TupleEntryControls.bigMarker

def ps (loc : AbiEntry.Loc) : List Param :=
  [{shape := .word (.uint 8),loc},{shape := .word .bool,loc},{shape := .word (.enumBelow 3),loc},
   {shape := .word (.int 8),loc},{shape := .word (.fixedBytes 32),loc},{shape := .word (.uint 256),loc}]
def vals (loc : AbiEntry.Loc) : Vals ((ps loc).map Param.shape) :=
  .cons (.word u8) (.cons (.word b1) (.cons (.word en) (.cons (.word neg) (.cons (.word fb) (.cons (.word big) .nil)))))

theorem shapes (loc : AbiEntry.Loc) : WordShapes ((ps loc).map Param.shape) := by
  intro s hs
  simp only [ps,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_,rfl⟩

def sample (loc : AbiEntry.Loc) := WordListReadback.input (ps loc) (vals loc) sel post 128

theorem uniform (loc : AbiEntry.Loc) : ∃ es : Entries (ps loc),
    enter (sample loc) 2 (ps loc) 0 0 = .ok (es,0) ∧ entry (sample loc) 2 (ps loc) = .ok es ∧
    bodyValues (sample loc) 2 (ps loc) es 0 = .ok (vals loc) ∧ verdict (sample loc) 2 (ps loc) = .run (vals loc) ∧
    4 + headsOf (ps loc) ≤ lim :=
  WordListReadback.roundtrip (ps loc) (vals loc) sel post 128 2 (shapes loc) (by decide +kernel)
    (by
      simpa only [WordListReadback.input,Input.size,List.length_append,encoded_length _ (shapes loc),ps,
        List.length_map,List.length_cons,List.length_nil,sel,post,CanonicalControls.selector,CanonicalControls.trailing]
        using (by decide +kernel : 199 ≤ lim)) (by decide +kernel)

def repeatParams (n : Nat) (loc : AbiEntry.Loc) : List Param := List.replicate n {shape := .word (.uint 256),loc}
def repeatVals (loc : AbiEntry.Loc) : (n : Nat) → Vals ((repeatParams n loc).map Param.shape)
  | 0 => .nil
  | n + 1 => .cons (.word big) (repeatVals loc n)

theorem repeatShapes (n : Nat) (loc : AbiEntry.Loc) : WordShapes ((repeatParams n loc).map Param.shape) := by
  induction n with
  | zero => intro s hs; cases hs
  | succ n ih =>
    intro s hs
    change s ∈ .word (.uint 256) :: (repeatParams n loc).map Param.shape at hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨.uint 256,rfl⟩
    · exact ih s hs

/-- Actual inhabited generic client at arbitrary length, not a fixed tuple. -/
theorem repeated (n : Nat) (loc : AbiEntry.Loc) (selector suffix : List UInt8) (free : Nat)
    (hsel : selector.length = 4)
    (size : (WordListReadback.input (repeatParams n loc) (repeatVals loc n) selector suffix free).size ≤ lim) :
    ∃ es, entry (WordListReadback.input (repeatParams n loc) (repeatVals loc n) selector suffix free) 2 (repeatParams n loc) = .ok es ∧
      bodyValues (WordListReadback.input (repeatParams n loc) (repeatVals loc n) selector suffix free) 2 (repeatParams n loc) es 0 = .ok (repeatVals loc n) := by
  obtain ⟨es,en,ep,body,run,bound⟩ := WordListReadback.roundtrip _ _ selector suffix free 2
    (repeatShapes n loc) hsel size (by decide)
  exact ⟨es,ep,body⟩

def tupleI : Input := ⟨sel ++ encodeArgs (tupleValues (vals .value)) ++ post,128⟩

theorem tuple_typed (lazy : Bool) : ∃ es : Entries (tupleParams ((ps .value).map Param.shape) lazy),
    enter tupleI 10 (tupleParams ((ps .value).map Param.shape) lazy) 0 0 = .ok (es,if lazy then 0 else 192) ∧
    entry tupleI 10 (tupleParams ((ps .value).map Param.shape) lazy) = .ok es ∧
    bodyValues tupleI 10 (tupleParams ((ps .value).map Param.shape) lazy) es 0 = .ok (tupleValues (vals .value)) ∧
    verdict tupleI 10 (tupleParams ((ps .value).map Param.shape) lazy) = .run (tupleValues (vals .value)) ∧
    cval tupleI 9 (.tuple ((ps .value).map Param.shape)) 4 0 = .ok (.tuple (vals .value)) :=
  tuple_roundtrip _ (vals .value) sel post 128 10 lazy (shapes .value) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem same_bytes_distinct_cost : tupleI.data = (sample .memory).data ∧ (encodeArgs (vals .value)).length = 192 := by
  constructor
  · unfold tupleI sample WordListReadback.input
    rw [tuple_encoded _ _ (shapes .value)]
    rfl
  · exact encoded_length _ (shapes .value)

private theorem failed {ε α : Type} (x : Except ε α) (e : ε)
    (h : (match x with | .error a => some a | .ok _ => none) = some e) : x = .error e := by
  cases x with
  | error a => cases h; rfl
  | ok a => cases h

def badEnum : Input := ⟨sel ++ AbiEntry.wordBytes 255 ++ AbiEntry.wordBytes 1 ++ AbiEntry.wordBytes 3 ++
  AbiEntry.wordBytes neg.val ++ AbiEntry.wordBytes fb.val ++ AbiEntry.wordBytes big.val,128⟩
def badHigh : Input := ⟨sel ++ AbiEntry.wordBytes 256 ++ (encodeArgs (vals .value)).drop 32,128⟩
def short : Input := ⟨(sel ++ encodeArgs (vals .value)).take 195,128⟩

theorem malformed : entry badEnum 2 (ps .value) = .error .revert ∧ entry badHigh 2 (ps .value) = .error .revert ∧
    entry short 2 (ps .value) = .error .revert ∧ entry short 2 (ps .calldata) = .error .revert ∧
    (Kind.valid (.uint 8) 3 = true ∧ Kind.valid (.enumBelow 3) 3 = false) := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),
    failed _ _ (by decide +kernel),by decide +kernel⟩

def tupleBoundary : Input := ⟨tupleI.data,lim - 192⟩
def tupleOver : Input := ⟨tupleI.data,lim - 191⟩

theorem tuple_boundary : ∃ es, entry tupleBoundary 10 (tupleParams ((ps .value).map Param.shape) false) = .ok es ∧
    bodyValues tupleBoundary 10 (tupleParams ((ps .value).map Param.shape) false) es 0 = .ok (tupleValues (vals .value)) := by
  obtain ⟨es,en,ep,body,run,lazy⟩ := tuple_roundtrip _ (vals .value) sel post (lim - 192) 10 false
    (shapes .value) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨es,ep,body⟩

theorem fuel_and_allocation : entry (sample .value) 1 (ps .value) = .error .fuel ∧
    entry tupleI 2 (tupleParams ((ps .value).map Param.shape) false) = .error .fuel ∧
    entry tupleOver 10 (tupleParams ((ps .value).map Param.shape) false) = .error .panic ∧
    (verdict badEnum 2 (ps .calldata)).kind = "blocked: calldata element fails only on access: needs access-time calldata semantics" := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),by decide +kernel⟩

def seven : Word (.uint 8) := ⟨7,by decide +kernel,by decide +kernel⟩
def fixedSeq : Seq (.word (.uint 8)) 2 := .cons (.word u8) (.cons (.word seven) .nil)
def pre : List UInt8 := [9,0,255]
def suffix : List UInt8 := [17,0]
def fixedI : Input := ⟨pre ++ Val.enc (.fixed fixedSeq) ++ suffix,128⟩
def fixedBoundary : Input := ⟨fixedI.data,lim - 64⟩
def fixedOver : Input := ⟨fixedI.data,lim - 63⟩
def fixedShort : Input := ⟨pre ++ (Val.enc (.fixed fixedSeq)).take 63,128⟩
def fixedShortTight : Input := ⟨fixedShort.data,lim - 63⟩

theorem fixed_typed : mdec fixedI 5 (.fixed (.word (.uint 8)) 2) 3 0 = .ok (.fixed fixedSeq,64) ∧
    mdec fixedBoundary 5 (.fixed (.word (.uint 8)) 2) 3 0 = .ok (.fixed fixedSeq,64) :=
  ⟨mdec_fixed fixedSeq fixedI pre suffix 0 5 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel),
   mdec_fixed fixedSeq fixedBoundary pre suffix 0 5 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem fixed_failures : mdec fixedOver 5 (.fixed (.word (.uint 8)) 2) 3 0 = .error .panic ∧
    mdec fixedShort 5 (.fixed (.word (.uint 8)) 2) 3 0 = .error .revert ∧
    mdec fixedShortTight 5 (.fixed (.word (.uint 8)) 2) 3 0 = .error .panic ∧
    mdec fixedBoundary 5 (.fixed (.word (.uint 8)) 2) 3 1 = .error .panic := by
  exact ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

def emptyFixed : Seq (.word (.uint 8)) 0 := .nil
def emptyFixedI : Input := ⟨pre ++ List.replicate 32 0,128⟩
def emptyFixedShort : Input := ⟨pre,lim + 1⟩

theorem fixed_zero_header : mdec emptyFixedI 3 (.fixed (.word (.uint 8)) 0) 3 0 = .ok (.fixed emptyFixed,0) ∧
    mdec emptyFixedShort 3 (.fixed (.word (.uint 8)) 0) 3 0 = .error .revert :=
  ⟨mdec_fixed emptyFixed emptyFixedI pre (List.replicate 32 0) 0 3 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel),failed _ _ (by decide +kernel)⟩

/-- Empty flat lists allocate nothing; empty tuple still runs real alloc0.
These are intrinsic controls, not admission of empty Source aggregates. -/
theorem empty_contrast :
    EntryTransport.bodyObservation ⟨sel,lim + 1⟩ 0 [] encodeArgs = some [] ∧
    entry ⟨sel,lim + 1⟩ 4 (tupleParams [] false) = .error .panic ∧
    EntryTransport.bodyObservation ⟨sel,128⟩ 2 (tupleParams [] false) encodeArgs = some [] := by
  exact ⟨by decide +kernel,failed _ _ (by decide +kernel),by decide +kernel⟩

theorem wrong_order : encodeArgs (vals .value) ≠ (encodeArgs (vals .value)).reverse ∧
    load (sample .value).data 4 = 255 ∧ load (sample .value).data 36 = 1 ∧ load (sample .value).data 68 = 2 ∧
    load (sample .value).data 100 = AbiEntry.W - 1 ∧ load (sample .value).data 132 = 300 ∧
    load (sample .value).data 164 = AbiEntry.W - 1 := by decide +kernel



def mixedPs : List Param :=
  [{shape := .word (.uint 8),loc := .value},{shape := .word .bool,loc := .memory},
   {shape := .word (.enumBelow 3),loc := .calldata,readsOnly := true},
   {shape := .word (.int 8),loc := .calldata},{shape := .word (.fixedBytes 32),loc := .value},
   {shape := .word (.uint 256),loc := .memory}]

theorem mixed_typed : ∃ es, entry (sample .value) 2 mixedPs = .ok es ∧
    bodyValues (sample .value) 2 mixedPs es 0 = .ok (vals .value) := by
  obtain ⟨es,en,ep,body,run,bound⟩ := WordListReadback.roundtrip mixedPs (vals .value) sel post 128 2
    (shapes .value) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨es,ep,body⟩

def zeroEnum : Word (.enumBelow 3) := ⟨0,by decide +kernel,by decide +kernel⟩
def enumSeq : Seq (.word (.enumBelow 3)) 2 := .cons (.word en) (.cons (.word zeroEnum) .nil)
def arrayI : Input := ⟨pre ++ Val.enc (.array enumSeq) ++ suffix,128⟩
def badArray : Input := ⟨pre ++ AbiEntry.wordBytes 2 ++ AbiEntry.wordBytes 3 ++ AbiEntry.wordBytes 0,128⟩

theorem array_typed : mdec arrayI 5 (.array (.word (.enumBelow 3))) 3 0 = .ok (.array enumSeq,96) :=
  mdec_word_array enumSeq arrayI pre suffix 0 5 rfl (by decide +kernel) (by decide +kernel)

theorem array_failures : mdec badArray 5 (.array (.word (.enumBelow 3))) 3 0 = .error .revert ∧
    mdec badArray 2 (.array (.word (.enumBelow 3))) 3 0 = .error .fuel :=
  ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

theorem offset_positive : melem (sample .value) 2 (.word (.uint 8)) 4 4 0 = .ok (.word u8,0) :=
  word_melem (sample .value) (.uint 8) u8 0 0 2 (by decide +kernel) (by decide +kernel)

theorem wrong_offset : melem (sample .value) 2 (.word (.uint 8)) 4 5 0 = .error .revert :=
  failed _ _ (by decide +kernel)

theorem arbitrary_cursor : ∃ es, enter (sample .memory) 2 (ps .memory) 0 17 = .ok (es,17) ∧
    bodyValues (sample .memory) 2 (ps .memory) es 0 = .ok (vals .memory) :=
  window (ps .memory) (vals .memory) (sample .memory) sel post 0 17 2 (shapes .memory) rfl
    (by decide +kernel) (by decide +kernel)

def tupleBadTight : Input := ⟨badEnum.data,lim - 191⟩

theorem tuple_bad_priority : mdec badEnum 9 (.tuple ((ps .value).map Param.shape)) 4 0 = .error .revert ∧
    mdec tupleBadTight 9 (.tuple ((ps .value).map Param.shape)) 4 0 = .error .panic :=
  ⟨failed _ _ (by decide +kernel),failed _ _ (by decide +kernel)⟩

/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.shapes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms shapes
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.uniform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uniform
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.repeatShapes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms repeatShapes
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.repeated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeated
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.tuple_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tuple_typed
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.same_bytes_distinct_cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms same_bytes_distinct_cost
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.malformed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms malformed
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.tuple_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tuple_boundary
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.fuel_and_allocation' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms fuel_and_allocation
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.fixed_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_typed
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.fixed_failures' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fixed_failures
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.fixed_zero_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_zero_header
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.empty_contrast' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms empty_contrast
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.wrong_order' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_order
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.mixed_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_typed
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.array_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_typed
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.array_failures' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms array_failures
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.offset_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms offset_positive
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.wrong_offset' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_offset
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.arbitrary_cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arbitrary_cursor
/-- info: 'Solidity.Backend.AbiWorld.UniformWordControls.tuple_bad_priority' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tuple_bad_priority
end Solidity.Backend.AbiWorld.UniformWordControls
