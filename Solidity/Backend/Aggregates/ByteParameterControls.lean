import Solidity.Backend.Aggregates.ByteParameters

/-! Inhabited controls on the actual raw Source frame and typed target heap.
No external compiler/EVM execution is asserted. -/
namespace Solidity.Backend.Aggregates.ByteParameterControls
open Solidity ByteParameters

def selector : Roadmap.Bytes := [1,2,3,4]
def data : Roadmap.Bytes := List.replicate 31 0 ++ [32] ++
  List.replicate 31 0 ++ [3] ++ [7,8,9] ++ List.replicate 29 0

def frame : Source.Fr := { this := ⟨1,by decide⟩, sender := ⟨2,by decide⟩, value := ⟨0,by decide⟩, static := false, contract := "C", cd := selector ++ data }

theorem entry : Source.cdTail data 0 1 = .ok (68,3) := by
  have offset : Source.wordAt data 0 = 32 := by decide
  have count : Source.wordAt (data.drop 32) 0 = 3 := by decide
  have size : data.length = 96 := by decide
  simp only [Source.cdTail,offset,count,size]
  rfl
theorem exact_extent : (ByteParameters.payload frame 68 3).length = 3 :=
  entry_payload_exact frame selector data rfl rfl entry

def C : Contract := { vars := [] }
def oldObject := bytesObj [] [170,187] (by decide)
def oldTarget := (State.init C).allocPush oldObject
def aliasTarget := oldTarget.push (t := .mem bytesR)
  (some ((State.init C).alloc oldObject).2)

def capacity : (ByteParameters.payload frame 68 3).length < 2^256 := entry_capacity frame entry
def lowered := lower aliasTarget frame 68 3 capacity

theorem old_aliases : TEnv.get (.there .here) lowered.env =
    TEnv.get (.there (.there .here)) lowered.env := rfl

theorem fresh_id : (aliasTarget.alloc (bytesObj aliasTarget.H
    (ByteParameters.payload frame 68 3) capacity)).2.id = 1 := rfl

theorem fresh_contents : MObj.elems ArrTy.dyn (lowered.heap.get
    (aliasTarget.alloc (bytesObj aliasTarget.H (ByteParameters.payload frame 68 3) capacity)).2) =
    [7,8,9].map byteWord := target_contents aliasTarget frame 68 3 capacity

theorem old_contents : MObj.elems ArrTy.dyn (lowered.heap.get
    (HRef.wk (List.prefix_append aliasTarget.H [bytesR])
      ((State.init C).alloc oldObject).2)) = [170,187].map byteWord := by
  unfold lowered
  have kept := target_old_heap aliasTarget frame 68 3 capacity
    ((State.init C).alloc oldObject).2
  rw [kept]
  change MObj.elems ArrTy.dyn (MObj.wk _ bytesR
    (oldTarget.heap.get ((State.init C).alloc oldObject).2)) = _
  unfold oldTarget
  rw [State.allocPush_get]
  simp only [oldObject,bytesObj,wordsObj,MObj.wk,MObj.elems_dyn,List.map_map]
  rfl

def E : Source.Env := ⟨[]⟩
def sourceHeap : Source.Heap E.layout :=
  ((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [170,187]⟩).1.alloc
    ⟨.bytes .memory,.bytes [204]⟩).1

def sourceState : Source.St E :=
  ⟨⟨⟨fun _ => Source.Account.empty _⟩, Source.Transient.empty, []⟩,
    sourceHeap, [], [], ⟨[], .nil⟩, Source.FailureExecution.Cursor.empty⟩
def sourceLocals : Source.Locals E.layout [.bytes .memory,.bytes .memory] :=
  .cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)
def sourceBefore := (sourceLocals,sourceState)

theorem related : Related
    ((Source.cdToMem frame (.bytes .memory) 68 3).run sourceBefore).2.2.heap
    2 lowered.heap (aliasTarget.alloc (bytesObj aliasTarget.H
      (ByteParameters.payload frame 68 3) capacity)).2 :=
  copy_related frame 68 3 sourceBefore aliasTarget capacity

theorem source_old_object :
    ((Source.cdToMem frame (.bytes .memory) 68 3).run sourceBefore).2.2.heap.get 0 =
      some ⟨.bytes .memory,.bytes [170,187]⟩ := rfl

theorem distinct_source_target_ids : sourceHeap.next ≠
    (aliasTarget.alloc (bytesObj aliasTarget.H (ByteParameters.payload frame 68 3) capacity)).2.id := by decide

theorem slice : Source.sliceR (D := E.layout)
    (Source.Val.cdRef (τ := .bytes .calldata) rfl 68 3) 1 3 false =
    .ok (.cdRef rfl 69 2) := rfl

theorem reversed_slice : Source.sliceR (D := E.layout)
    (Source.Val.cdRef (τ := .bytes .calldata) rfl 68 3) 3 1 false =
    .error (.revert []) := rfl

theorem past_end_slice : Source.sliceR (D := E.layout)
    (Source.Val.cdRef (τ := .bytes .calldata) rfl 68 3) 0 4 false =
    .error (.revert []) := rfl

theorem truncated_entry : Source.cdTail (List.replicate 31 0 ++ [32] ++
    List.replicate 31 0 ++ [3] ++ [7]) 0 1 = .error (.revert []) := by
  let short : Roadmap.Bytes := List.replicate 31 0 ++ [32] ++
    List.replicate 31 0 ++ [3] ++ [7]
  change Source.cdTail short 0 1 = _
  have offset : Source.wordAt short 0 = 32 := by decide
  have count : Source.wordAt (short.drop 32) 0 = 3 := by decide
  have size : short.length = 65 := by decide
  simp only [Source.cdTail,offset,count,size]
  rfl

theorem omitted_selector_wrong : ByteParameters.payload {frame with cd := data} 68 3 ≠ [7,8,9] := by decide

theorem empty_payload : ByteParameters.payload frame 71 0 = [] := rfl

def emptyLowered := lower aliasTarget frame 71 0 (by decide)
theorem empty_contents : MObj.elems ArrTy.dyn (emptyLowered.heap.get
    (aliasTarget.alloc (bytesObj aliasTarget.H [] (by decide))).2) = [] :=
  target_contents aliasTarget frame 71 0 (by decide)

def otherFrame : Source.Fr := {frame with cd := (frame.cd.take 68) ++ [17,18,19]}
def otherLowered := lower aliasTarget otherFrame 68 3 (by decide)
theorem runtime_input_matters : MObj.elems ArrTy.dyn (otherLowered.heap.get
    (aliasTarget.alloc (bytesObj aliasTarget.H [17,18,19] (by decide))).2) =
      [17,18,19].map byteWord :=
  target_contents aliasTarget otherFrame 68 3 (by decide)

theorem wrong_contents : [7,8,9].map byteWord ≠ [17,18,19].map byteWord := by decide

theorem entry_reference : ∃ value,
    Source.cdArg E.layout data 0 1 (τ := .bytes .calldata) rfl = .ok value ∧
      RefRelated frame value lowered.heap
        (aliasTarget.alloc (bytesObj aliasTarget.H (ByteParameters.payload frame 68 3) capacity)).2 ∧
      (ByteParameters.payload frame 68 3).length = 3 :=
  raw_parameter_related E.layout aliasTarget frame selector data rfl rfl entry

end Solidity.Backend.Aggregates.ByteParameterControls
