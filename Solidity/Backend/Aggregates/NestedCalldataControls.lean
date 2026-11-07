import Solidity.Source.CalldataAggregates
import Solidity.Backend.Aggregates.ByteSliceControls

/-! Inhabited actual Source decoder/read/expression clients, preserving the
existing value API. Compiler acceptance is checked separately; no EVM runtime
execution or general lowering is asserted by these local controls. -/
namespace Solidity.Backend.Aggregates.NestedCalldataControls
open Solidity ByteParameterControls

abbrev caller : Source.RCtx := [.bytes .memory,.bytes .memory]
abbrev uint : Source.STy := .int Source.IntTy.u256
abbrev nestedTy : Source.STy := .array .calldata (.bytes .calldata) none
abbrev staticChild : Source.STy := .array .calldata uint (some 2)
abbrev staticTy : Source.STy := .array .calldata staticChild none

def word (n : Nat) : Roadmap.Bytes := List.replicate 31 0 ++ [UInt8.ofNat n]
def nestedData : Roadmap.Bytes := word 32 ++ word 2 ++ word 64 ++ word 128 ++
  word 1 ++ [17] ++ List.replicate 31 0 ++ word 2 ++ [34,51] ++ List.replicate 30 0

def nestedFrame : Source.Fr := {frame with cd := selector ++ nestedData}
def truncatedFrame : Source.Fr := {nestedFrame with cd := selector ++ nestedData.take 224}

theorem nested_entry : Source.cdTail nestedData 0 32 = .ok (68,2) := by
  have offset : Source.wordAt nestedData 0 = 32 := by decide +kernel
  have count : Source.wordAt (nestedData.drop 32) 0 = 2 := by decide +kernel
  have size : nestedData.length = 256 := by decide +kernel
  simp only [Source.cdTail,offset,count,size]
  rfl

theorem root_decodes : (Source.decodeArg nestedData 0 nestedTy).run sourceBefore =
    (.ok (.cdRef rfl 68 2),sourceBefore) := by
  rw [Source.decodeArg_cdArray_run nestedData 0 (.bytes .calldata) rfl sourceBefore]
  change (Source.cdArg E.layout nestedData 0 32 rfl,sourceBefore) = _
  rw [Source.cdArg,nested_entry]
  rfl

theorem second_tail : Source.cdNested nestedFrame 68 1 1 = .ok (228,2) := by
  have offset : Source.wordAt (nestedFrame.cd.drop 68) 1 = 128 := by decide +kernel
  have count : Source.wordAt ((nestedFrame.cd.drop 68).drop 128) 0 = 2 := by decide +kernel
  have size : (nestedFrame.cd.drop 68).length = 192 := by decide +kernel
  have tail : Source.cdTail (nestedFrame.cd.drop 68) 1 1 = .ok (164,2) := by
    simp only [Source.cdTail,offset,count,size]
    rfl
  unfold Source.cdNested
  rw [tail]
  rfl

theorem read_second : (Source.readLoc nestedFrame (.cdBytes 68 1)).run sourceBefore =
    (.ok (.cdRef rfl 228 2),sourceBefore) := by
  rw [Source.readLoc_cdBytes_run,second_tail]
  rfl

def beforeOne : Source.Locals E.layout (nestedTy :: uint :: caller) × Source.St E :=
  (.cons (.cdRef rfl 68 2) (.cons (.int 1 (by decide +kernel)) sourceLocals),sourceState)
def beforeTwo : Source.Locals E.layout (nestedTy :: uint :: caller) × Source.St E :=
  (.cons (.cdRef rfl 68 2) (.cons (.int 2 (by decide +kernel)) sourceLocals),sourceState)
def indexExpr : Source.RExpr E (nestedTy :: uint :: caller) (.bytes .calldata) :=
  .indexArray (.local .here) (.local (.there .here)) rfl

theorem eval_second : (Source.evalE ByteSliceControls.G nestedFrame 2 indexExpr).run beforeOne =
    (.ok (.val (.cdRef rfl 228 2)),beforeOne) := by
  unfold indexExpr beforeOne
  refine Eq.trans (Source.eval_cdIndex_run ByteSliceControls.G nestedFrame 0 (.bytes .calldata) 68 2 1 (by decide) sourceLocals sourceState) ?_
  rw [Source.indexLoc_cdBytes_eq nestedFrame 68 2 1 (by decide),pure_bind]
  rw [Source.Hoare.run_bind,Source.readLoc_cdBytes_run,second_tail]
  rfl

theorem child_payload : ByteParameters.payload nestedFrame 228 2 = [34,51] := by decide +kernel

theorem truncated_tail : Source.cdNested truncatedFrame 68 1 1 = .error (.revert []) := by
  have offset : Source.wordAt (truncatedFrame.cd.drop 68) 1 = 128 := by decide +kernel
  have count : Source.wordAt ((truncatedFrame.cd.drop 68).drop 128) 0 = 2 := by decide +kernel
  have size : (truncatedFrame.cd.drop 68).length = 160 := by decide +kernel
  unfold Source.cdNested
  simp only [Source.cdTail,offset,count,size]
  rfl

theorem truncated_read : (Source.readLoc truncatedFrame (.cdBytes 68 1)).run sourceBefore =
    (.error (.revert []),sourceBefore) := by
  rw [Source.readLoc_cdBytes_run,truncated_tail]
  rfl

theorem parent_bounds_first : (Source.evalE ByteSliceControls.G truncatedFrame 2 indexExpr).run beforeTwo =
    (.error (.revert (Source.panicData .index)),beforeTwo) := by
  unfold indexExpr beforeTwo
  refine Eq.trans (Source.eval_cdIndex_run ByteSliceControls.G truncatedFrame 0 (.bytes .calldata) 68 2 2 (by decide) sourceLocals sourceState) ?_
  rfl

def staticData : Roadmap.Bytes := word 32 ++ word 2 ++ word 10 ++ word 11 ++ word 20 ++ word 21
def staticFrame : Source.Fr := {frame with cd := selector ++ staticData}

theorem static_entry : Source.cdTail staticData 0 64 = .ok (68,2) := by
  have offset : Source.wordAt staticData 0 = 32 := by decide +kernel
  have count : Source.wordAt (staticData.drop 32) 0 = 2 := by decide +kernel
  have size : staticData.length = 192 := by decide +kernel
  simp only [Source.cdTail,offset,count,size]
  rfl

theorem static_slice : Source.sliceR (Source.Val.cdRef (D := E.layout) (τ := staticTy) rfl 68 2)
    1 2 false = .ok (.cdRef rfl 132 1) := rfl

theorem wrong_static_stride : Source.sliceR (Source.Val.cdRef (D := E.layout) (τ := staticTy) rfl 68 2)
    1 2 false ≠ .ok (.cdRef rfl 100 1) := by
  rw [static_slice]
  intro impossible
  cases impossible

def staticBefore : Source.Locals E.layout (staticTy :: uint :: uint :: uint :: uint :: caller) × Source.St E :=
  (.cons (.cdRef rfl 68 2) (.cons (.int 1 (by decide +kernel)) (.cons (.int 2 (by decide +kernel))
    (.cons (.int 0 (by decide +kernel)) (.cons (.int 1 (by decide +kernel)) sourceLocals)))),sourceState)
def staticExpr : Source.RExpr E (staticTy :: uint :: uint :: uint :: uint :: caller) uint :=
  .indexArray
    (.indexArray (.slice (.local .here) rfl (.local (.there .here)) rfl
      (.local (.there (.there .here))) rfl false)
      (.local (.there (.there (.there .here)))) rfl)
    (.local (.there (.there (.there (.there .here))))) rfl

theorem static_word : Source.cdWordAt staticFrame 164 = 21 := by decide +kernel

theorem eval_static_slice : (Source.evalE ByteSliceControls.G staticFrame 4 staticExpr).run staticBefore =
    (.ok (.val (.int 21 (by decide +kernel))),staticBefore) := by
  simp only [staticExpr,Source.evalE]
  change ((Source.EM.lift (Source.decodeWord E.layout (Source.cdWordAt staticFrame 164) uint)) >>=
    fun value => pure (Source.RVal.val value)).run staticBefore = _
  rw [static_word]
  rfl

theorem static_caller_aliases :
    staticBefore.1.get (.there (.there (.there (.there (.there .here))))) =
      staticBefore.1.get (.there (.there (.there (.there (.there (.there .here)))))) := rfl

theorem wrong_child_bytes : ByteParameters.payload nestedFrame 228 2 ≠ [51,34] := by decide +kernel

theorem wrong_empty_halt : ((Source.evalE ByteSliceControls.G truncatedFrame 2 indexExpr).run beforeTwo).1 ≠
    .error (.revert []) := by
  rw [parent_bounds_first]
  intro impossible
  cases impossible

theorem read_string_second : (Source.readLoc nestedFrame (.cdString 68 1)).run sourceBefore =
    (.ok (.cdRef rfl 228 2),sourceBefore) := by
  rw [Source.readLoc_cdString_run,second_tail]
  rfl

theorem string_copied :
    ((Source.cdToMem nestedFrame (.string .memory) 228 2).run sourceBefore).2.2.heap.get 2 =
      some ⟨.string .memory,.string [34,51]⟩ := by
  rw [Source.cdToMem_string_run]
  change (sourceState.heap.alloc
    ⟨.string .memory,.string ((nestedFrame.cd.drop 228).take 2)⟩).1.get sourceState.heap.next = _
  have fresh := Source.Heap.alloc_get sourceState.heap
    (⟨.string .memory,Source.Data.string ((nestedFrame.cd.drop 228).take 2)⟩ : Σ τ, Source.Data E.layout τ)
  refine Eq.trans fresh ?_
  exact congrArg (fun bytes => some (⟨.string .memory,Source.Data.string bytes⟩ : Σ τ, Source.Data E.layout τ)) child_payload

theorem readonly_string_write :
    (Source.writeLoc nestedFrame 0 (.cdString 68 1) (.cdRef rfl 228 2)).run sourceBefore =
      (.error (.stuck "calldata is read only"),sourceBefore) := rfl

def arraysData : Roadmap.Bytes := word 32 ++ word 2 ++ word 64 ++ word 160 ++
  word 2 ++ word 10 ++ word 11 ++ word 1 ++ word 21
def arraysFrame : Source.Fr := {frame with cd := selector ++ arraysData}
abbrev arraysTy : Source.STy := .array .calldata (.array .calldata uint none) none

theorem arrays_tail : Source.cdNested arraysFrame 68 1 32 = .ok (260,1) := by
  have offset : Source.wordAt (arraysFrame.cd.drop 68) 1 = 160 := by decide +kernel
  have count : Source.wordAt ((arraysFrame.cd.drop 68).drop 160) 0 = 1 := by decide +kernel
  have size : (arraysFrame.cd.drop 68).length = 224 := by decide +kernel
  unfold Source.cdNested
  simp only [Source.cdTail,offset,count,size]
  rfl

theorem read_array_second :
    (Source.readLoc arraysFrame (.cdArray (σ := uint) 68 1)).run sourceBefore =
      (.ok (.cdRef rfl 260 1),sourceBefore) := by
  rw [Source.readLoc_cdArray_run]
  change ((Source.cdNested arraysFrame 68 1 32).map _,sourceBefore) = _
  rw [arrays_tail]
  rfl

def arraysBefore : Source.Locals E.layout (arraysTy :: uint :: uint :: caller) × Source.St E :=
  (.cons (.cdRef rfl 68 2) (.cons (.int 1 (by decide))
    (.cons (.int 0 (by decide)) sourceLocals)),sourceState)
def arraysExpr : Source.RExpr E (arraysTy :: uint :: uint :: caller) uint :=
  .indexArray (.indexArray (.local .here) (.local (.there .here)) rfl)
    (.local (.there (.there .here))) rfl

theorem arrays_word : Source.cdWordAt arraysFrame 260 = 21 := by decide +kernel

theorem eval_arrays : (Source.evalE ByteSliceControls.G arraysFrame 3 arraysExpr).run arraysBefore =
    (.ok (.val (.int 21 (by decide))),arraysBefore) := by
  unfold arraysExpr arraysBefore
  refine Eq.trans (Source.eval_cdDoubleIndex_run ByteSliceControls.G arraysFrame 0 uint 68 2 1 0
    (by decide) (by decide) sourceLocals sourceState) ?_
  rw [Source.indexLoc_cdArray_eq arraysFrame uint 68 2 1 (by decide),pure_bind]
  rw [Source.Hoare.run_bind,Source.readLoc_cdArray_run]
  rw [Source.cdHeadBytes_of_word (τ := uint) rfl,arrays_tail]
  change ((Source.EM.lift (Source.decodeWord E.layout (Source.cdWordAt arraysFrame 260) uint)) >>=
    fun value => pure (Source.RVal.val value)).run arraysBefore = _
  rw [arrays_word]
  rfl

theorem truncated_string_read :
    (Source.readLoc truncatedFrame (.cdString 68 1)).run sourceBefore =
      (.error (.revert []),sourceBefore) := by
  rw [Source.readLoc_cdString_run,truncated_tail]
  rfl

end Solidity.Backend.Aggregates.NestedCalldataControls
