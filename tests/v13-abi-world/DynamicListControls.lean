import Solidity.Backend.AbiWorld.DynamicAggregateReadback
import tests.«v13-abi-world».UniformWordControls

/-! Actual arbitrary-list typed clients, mixed dynamic tuple allocation and
ordered failure controls. No source admission or runtime encoding claim. -/
namespace Solidity.Backend.AbiWorld.DynamicListControls
open AbiEntry DynamicListReadback

def selector := CanonicalControls.selector
def suffix := CanonicalControls.trailing
def ps (loc : AbiEntry.Loc) : List Param :=
  [{shape := .bytes,loc},{shape := .word (.uint 256),loc},
   {shape := .bytes,loc,readsOnly := true},{shape := .word (.enumBelow 3),loc}]
def vals (bs cs : List UInt8) (loc : AbiEntry.Loc) : Vals ((ps loc).map Param.shape) :=
  .cons (.bytes bs) (.cons (.word UniformWordControls.big) (.cons (.bytes cs) (.cons (.word UniformWordControls.en) .nil)))

theorem leaves (loc : AbiEntry.Loc) : LeafShapes ((ps loc).map Param.shape) := by
  intro s hs
  simp only [ps,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl ⟨_,rfl⟩
  · exact Or.inr rfl
  · exact Or.inl ⟨_,rfl⟩

def repeatParams (loc : AbiEntry.Loc) : Nat → List Param
  | 0 => []
  | n + 1 => {shape := .bytes,loc} :: {shape := .word (.uint 256),loc} :: repeatParams loc n

def repeatVals (bs : List UInt8) (loc : AbiEntry.Loc) : (n : Nat) → Vals ((repeatParams loc n).map Param.shape)
  | 0 => .nil
  | n + 1 => .cons (.bytes bs) (.cons (.word UniformWordControls.big) (repeatVals bs loc n))

theorem repeat_leaves (loc : AbiEntry.Loc) (n : Nat) : LeafShapes ((repeatParams loc n).map Param.shape) := by
  induction n with
  | zero => intro s hs; cases hs
  | succ n ih =>
    intro s hs
    change s ∈ .bytes :: .word (.uint 256) :: (repeatParams loc n).map Param.shape at hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · exact Or.inr rfl
    · exact Or.inl ⟨_,rfl⟩
    · exact ih s hs

theorem repeat_tail (bs : List UInt8) (loc : AbiEntry.Loc) (n : Nat) :
    tailSize (repeatVals bs loc n) = n * BytesReadback.allocationBytes bs := by
  induction n with
  | zero => change 0 = 0 * BytesReadback.allocationBytes bs; rw [Nat.zero_mul]
  | succ n ih =>
    simp only [repeatVals,tail_bytes,tail_word,ih,Nat.succ_mul]
    omega

/-- Inhabited at ARBITRARY list length, original fuel2, arbitrary selector and
suffix. Bounds concern actual input/allocation sizes, never uint byte range. -/
theorem repeated (n : Nat) (bs sel post : List UInt8) (loc : AbiEntry.Loc) (free : Nat)
    (hsel : sel.length = 4)
    (size : (input (repeatParams loc n) (repeatVals bs loc n) sel post free).size ≤ lim)
    (allocation : free + n * BytesReadback.allocationBytes bs ≤ lim) :
    ∃ es, entry (input (repeatParams loc n) (repeatVals bs loc n) sel post free) 2 (repeatParams loc n) = .ok es ∧
      bodyValues (input (repeatParams loc n) (repeatVals bs loc n) sel post free) 2
        (repeatParams loc n) es 0 = .ok (repeatVals bs loc n) := by
  obtain ⟨es,en,ep,body,run,head⟩ := roundtrip _ _ sel post free 2 (repeat_leaves loc n) hsel size
    (by simpa only [repeat_tail] using allocation) (by decide)
  exact ⟨es,ep,body⟩

def bs : List UInt8 := [0,255]
def cs : List UInt8 := (List.range 33).map UInt8.ofNat

theorem sample_cost (loc : AbiEntry.Loc) : tailSize (vals bs cs loc) = 160 := by
  simp only [vals,tail_bytes,tail_word]
  change BytesReadback.allocationBytes bs + (BytesReadback.allocationBytes cs + 0) = 160
  decide +kernel

def sample (loc : AbiEntry.Loc) := input (ps loc) (vals bs cs loc) selector suffix 128

theorem sample_typed (loc : AbiEntry.Loc) : ∃ es,
    enter (sample loc) 2 (ps loc) 0 0 = .ok (es,spent (ps loc) (vals bs cs loc)) ∧
    entry (sample loc) 2 (ps loc) = .ok es ∧
    bodyValues (sample loc) 2 (ps loc) es 0 = .ok (vals bs cs loc) ∧
    verdict (sample loc) 2 (ps loc) = .run (vals bs cs loc) ∧ 4 + headsOf (ps loc) ≤ lim :=
  roundtrip _ _ selector suffix 128 2 (leaves loc) (by decide +kernel)
    (by
      simp only [input,Input.size,List.length_append,encoded_length _ _ (leaves loc),sample_cost,
        ps,List.length_map,List.length_cons,List.length_nil,selector,suffix,CanonicalControls.selector,CanonicalControls.trailing]
      exact (by decide +kernel))
    (by rw [sample_cost]; exact (by decide +kernel)) (by decide +kernel)

def tupleI : Input := ⟨selector ++ encodeArgs (.cons (.tuple (vals bs cs .value)) .nil) ++ suffix,128⟩
def tuplePs (lazy : Bool) := StaticAggregateReadback.tupleParams ((ps .value).map Param.shape) lazy

theorem tuple_typed (lazy : Bool) : ∃ es,
    enter tupleI 8 (tuplePs lazy) 0 0 = .ok (es,if lazy then 0 else 288) ∧
    entry tupleI 8 (tuplePs lazy) = .ok es ∧
    bodyValues tupleI 8 (tuplePs lazy) es 0 = .ok (.cons (.tuple (vals bs cs .value)) .nil) ∧
    verdict tupleI 8 (tuplePs lazy) = .run (.cons (.tuple (vals bs cs .value)) .nil) := by
  have h := DynamicAggregateReadback.tuple_roundtrip _ (vals bs cs .value) selector suffix 128 8 lazy
    (leaves .value) (by decide +kernel) (by decide +kernel)
    (by
      rw [DynamicAggregateReadback.tuple_encoded _ _ (by decide +kernel)]
      simp only [List.length_append,MixedPacket.word_length,encoded_length _ _ (leaves .value),sample_cost,
        ps,List.length_map,List.length_cons,List.length_nil,selector,suffix,CanonicalControls.selector,CanonicalControls.trailing]
      exact (by decide +kernel))
    (by rw [sample_cost]; exact (by decide +kernel)) (by decide +kernel)
  have cost : ((ps .value).map Param.shape).length * 32 + tailSize (vals bs cs .value) = 288 := by
    rw [sample_cost]
    rfl
  rw [cost] at h
  exact h

def memoryCursor (I : Input) (f : Nat) (params : List Param) (a : Nat := 0) : Option Nat :=
  (enter I f params 0 a).toOption.map Prod.snd

def err {α : Type} (x : Except Fail α) : Nat :=
  match x with | .ok _ => 0 | .error .revert => 1 | .error .panic => 2 | .error .fuel => 3

/-- Full original-word observation, exact heads and sequential allocation. -/
theorem layout : load (sample .memory).data 4 = 128 ∧ load (sample .memory).data 36 = AbiEntry.W - 1 ∧
    load (sample .memory).data 68 = 192 ∧ load (sample .memory).data 100 = 2 ∧
    memoryCursor (sample .memory) 2 (ps .memory) = some 160 ∧
    memoryCursor (sample .calldata) 2 (ps .calldata) = some 0 ∧
    memoryCursor tupleI 8 (tuplePs false) = some 288 ∧
    memoryCursor tupleI 8 (tuplePs true) = some 0 := by decide +kernel

def exact : Input := {sample .memory with free := lim - 160}
def over : Input := {exact with free := exact.free + 1}
def tupleExact : Input := {tupleI with free := lim - 288}
def tupleOver : Input := {tupleExact with free := tupleExact.free + 1}
def wrongOffset : Input := ⟨selector ++ AbiEntry.wordBytes (lim + 1) ++ ((sample .memory).data.drop 36),128⟩
def truncated : Input := ⟨((sample .memory).data.take 210),128⟩
def wrongShape : List Param := [{shape := .word .bool,loc := .memory}]
def unpadded : Input := ⟨selector ++ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes 2 ++ bs,128⟩

theorem boundaries : memoryCursor exact 2 (ps .memory) = some 160 ∧ err (entry over 2 (ps .memory)) = 2 ∧
    memoryCursor tupleExact 8 (tuplePs false) = some 288 ∧ err (entry tupleOver 8 (tuplePs false)) = 2 ∧
    err (entry wrongOffset 2 (ps .memory)) = 1 ∧ err (entry wrongOffset 0 (ps .memory)) = 3 ∧
    err (entry truncated 2 (ps .memory)) = 1 ∧ err (entry truncated 0 (ps .memory)) = 3 ∧
    err (entry (sample .memory) 2 wrongShape) = 1 ∧
    memoryCursor (sample .memory) 2 (ps .memory) 17 = some 177 ∧
    memoryCursor (sample .memory) 2 (ps .memory) 17 ≠ some 160 ∧
    memoryCursor unpadded 2 (BytesReadback.params .memory) = some 64 := by decide +kernel

def cases : List (List UInt8) := [[],[0],[255],List.replicate 31 0,List.replicate 32 255,(List.range 33).map UInt8.ofNat]
def caseInput (bs : List UInt8) (loc : AbiEntry.Loc) := input (ps loc) (vals bs [255] loc) selector suffix 128

theorem byte_boundaries : cases.map (fun bs => (verdict (caseInput bs .memory) 2 (ps .memory)).kind) =
    List.replicate 6 "run" ∧
    cases.map (fun bs => memoryCursor (caseInput bs .memory) 2 (ps .memory)) =
      [some 96,some 128,some 128,some 128,some 128,some 160] := by decide +kernel

def swapped : Input := input (ps .memory) (vals cs bs .memory) selector suffix 128
def tupleWrongBase : Input := ⟨(tupleI.data.take 36) ++ AbiEntry.wordBytes 160 ++ (tupleI.data.drop 68),128⟩
def byteLatePanic : Input := {truncated with free := lim}

theorem negatives : (sample .memory).data ≠ swapped.data ∧
    load (sample .memory).data 4 ≠ 32 ∧ load (sample .memory).data 68 ≠ 160 ∧
    err (entry tupleWrongBase 8 (tuplePs false)) = 2 ∧
    err (entry byteLatePanic 2 (ps .memory)) = 2 ∧
    err (entry byteLatePanic 0 (ps .memory)) = 3 ∧
    err (entry tupleWrongBase 0 (tuplePs false)) = 3 := by decide +kernel


/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.leaves' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms leaves
/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.repeat_leaves' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms repeat_leaves
/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.repeat_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeat_tail
/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.repeated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeated
/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.sample_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sample_cost
/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.sample_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sample_typed
/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.tuple_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tuple_typed
/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.layout' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms layout
/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.boundaries' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms boundaries
/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.byte_boundaries' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms byte_boundaries
/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.negatives' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms negatives

def shortPayload : Input := ⟨(sample .memory).data.take 240,128⟩
def secondPanic : Input := {shortPayload with free := lim - 100}
def shortHeader : Input := {truncated with free := lim - 100}

/-- First object succeeds; second allocation precedes short payload, whereas
its truncated length header is checked before that second allocation. -/
theorem later_failure_priority : err (entry shortPayload 2 (ps .memory)) = 1 ∧
    err (entry secondPanic 2 (ps .memory)) = 2 ∧ err (entry shortHeader 2 (ps .memory)) = 1 ∧
    err (entry secondPanic 0 (ps .memory)) = 3 := by decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.DynamicListControls.later_failure_priority' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms later_failure_priority

end Solidity.Backend.AbiWorld.DynamicListControls
