import Solidity.Yul.Views.JointRetained
import Solidity.Yul.Views.CanonicalAliasControls
import Solidity.Yul.Views.AggregateWritebackControls

namespace Solidity.Yul.Views.Controls

def jointValues (_ : Fin 2) : Source.Val mixedLayout (.bytes .memory) := .memRef rfl 1
def jointWords (_ : Fin 2) : Roadmap.Word := 384
def jointPhysical := wordListView allChangedWords (dynamicUintView 2 (by decide) jointWords mixedPhysical 1152) 896

theorem joint_fields_decode : decodeCanonicalFields mixedPlacement mixedEntries (mixedLayout.fields mixedName) jointPhysical 896 = some allChangedFields := by
  apply decodeCanonicalFields_reads _ _ mixed_coverage all_changed_fields_encoded
    (fun τ member => Or.inl (mixed_member_support τ member))
  exact fun i w found => wordList_read _ _ _ i w found

theorem joint_array_decode : decodeCanonicalArray mixedPlacement mixedEntries (.bytes .memory) 2 jointPhysical 1184 = some jointValues := by
  apply decodeCanonicalArray_reads _ _ mixed_coverage _ (Or.inl (Or.inr (Or.inr rfl))) 2 jointValues jointWords
    (fun _ => .pointer rfl 1 (.string .memory) rfl rfl)
  intro i
  rw [mload_congr jointPhysical (dynamicUintView 2 (by decide) jointWords mixedPhysical 1152) (1184 + i.val * 32)
    (fun j => wordList_residual _ _ _ _ (Or.inr (by have hi := j.isLt; change 896 + 5 * 32 ≤ 1184 + i.val * 32 + j.val; omega)))]
  exact dynamicUint_element 2 (by decide) jointWords mixedPhysical 1152 i

theorem joint_header : arrayLengthChoice none jointPhysical 1152 = 2 := by
  change (mload jointPhysical 1152).val = 2
  rw [mload_congr jointPhysical (dynamicUintView 2 (by decide) jointWords mixedPhysical 1152) 1152
    (fun j => wordList_residual _ _ _ _ (Or.inr (by have hi := j.isLt; change 896 + 5 * 32 ≤ 1152 + j.val; omega))), dynamicUint_header]

def jointHeap := pairWrittenHeap mixedHeap 3 (.struct allChangedFields) (by rfl) 4
  (dynamicMemberData mixedLayout (.bytes .memory) 2 jointValues) (by rfl)
def jointState := withSourceHeap mixedState jointHeap

theorem joint_source_step : canonicalJointState mixedState mixedPlacement mixedEntries 3 mixedName 4 (.bytes .memory) none 2
    (fun _ e => nomatch e) false jointPhysical = some (.ok (),jointState) := by
  have first := canonicalJoint_decoded mixedState mixedPlacement mixedEntries 3 mixedName 4 (.bytes .memory) none 2
    (fun _ e => nomatch e) jointPhysical joint_header allChangedFields jointValues joint_fields_decode joint_array_decode
  have second := twoHeapPut_run mixedState 3 (Source.Data.struct (l := .memory) allChangedFields) 4
    (dynamicMemberData mixedLayout (.bytes .memory) 2 jointValues) (by rfl) (by rfl)
  exact first.trans (congrArg some second)

theorem joint_both_orders : canonicalJointState mixedState mixedPlacement mixedEntries 3 mixedName 4 (.bytes .memory) none 2
    (fun _ e => nomatch e) true jointPhysical = some (.ok (),jointState) := by
  rw [← canonicalJoint_order _ _ _ _ _ _ _ _ _ _ (by rfl) (by rfl) (by decide)]
  exact joint_source_step

theorem joint_all_H_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H jointState :=
  canonicalJoint_MemOK H mixedState mixedPlacement mixedEntries 3 mixedName 4 (.bytes .memory) none 2 (fun _ e => nomatch e)
    false jointPhysical _ joint_source_step ok

theorem joint_actual_inhabited_MemOK : Source.MemOK mixedEnv mixedHeap.ty jointState := joint_all_H_MemOK _ mixed_actual_MemOK

theorem joint_actual_geometry : ∃ q : Placement jointHeap, q.address = mixedPlacement.address ∧ q.shape = mixedPlacement.shape ∧ q.free = mixedPlacement.free ∧
    ∃ entries : List (MixedHeapEntry q), CoversMixedHeap entries ∧ ∀ τ w, decodeExtendedMemoryMember q entries τ w = decodeExtendedMemoryMember mixedPlacement mixedEntries τ w :=
  canonicalJoint_geometry mixedPlacement mixedEntries mixed_coverage 3 mixedName mixedFields allChangedFields rfl 4 (.bytes .memory) none 2
    (fun _ e => nomatch e) retainedRefOld jointValues rfl jointPhysical joint_fields_decode joint_array_decode

theorem joint_other_roots : jointHeap.get 0 = mixedHeap.get 0 ∧ jointHeap.get 1 = mixedHeap.get 1 ∧ jointHeap.get 2 = mixedHeap.get 2 ∧
    jointHeap.get 5 = mixedHeap.get 5 ∧ jointHeap.ty = mixedHeap.ty ∧ jointHeap.next = mixedHeap.next ∧
    jointState.1 = mixedState.1 ∧ jointState.2.ex = mixedState.2.ex := by
  refine ⟨rfl,rfl,rfl,rfl,(pairWritten_preserves _ _ _ _ _ _ _).1,rfl,rfl,rfl⟩

def jointAliasState : Source.EMState mixedEnv [mixedArrayTy,mixedArrayTy] :=
  ⟨.cons (.memRef rfl 4) (.cons (.memRef rfl 4) .nil),mixedState.2⟩
def jointAliasAfter := withSourceHeap jointAliasState jointHeap

def readJointAlias (first : Bool) (index horizon : Nat) : Source.EM mixedEnv [mixedArrayTy,mixedArrayTy] (List UInt8) := do
  let locals ← Source.EM.locals
  let pointer := locals.get (if first then .here else .there .here)
  let loc ← Source.indexLoc mixedReadFrame pointer index
  let child ← Source.readLoc mixedReadFrame loc
  Source.bytesOfRV mixedReadFrame horizon (.val child)

theorem joint_real_alias_reads (horizon : Nat) :
    (readJointAlias true 0 horizon).run jointAliasAfter = (.ok mixedString,jointAliasAfter) ∧
    (readJointAlias false 1 horizon).run jointAliasAfter = (.ok mixedString,jointAliasAfter) ∧
    (readMixedMemberBytes 2 horizon).run jointState = (.ok mixedString,jointState) ∧
    (readMixedMemberBytes 3 horizon).run jointState = (.ok mixedString,jointState) := ⟨rfl,rfl,rfl,rfl⟩

theorem joint_real_alias_error (horizon : Nat) : (readJointAlias false 2 horizon).run jointAliasAfter =
    (.error (.revert (Source.panicData .index)),jointAliasAfter) := rfl

theorem joint_residual (a : Nat) (outsideStruct : a < 896 ∨ 1056 ≤ a) (outsideArray : a < 1152 ∨ 1248 ≤ a) : jointPhysical a = mixedPhysical a := by
  rw [jointPhysical, wordList_residual _ _ _ _ outsideStruct, dynamicUint_residual _ _ _ _ _ _ outsideArray]

theorem joint_nonzero_padding : jointPhysical 1056 = 0xa5 ∧ jointPhysical 1248 = 0xa5 ∧ jointPhysical 163 = 0xa5 ∧
    jointPhysical 64 = mixedPhysical 64 ∧ jointPhysical 96 = mixedPhysical 96 := by
  rw [joint_residual 1056 (Or.inr (by decide)) (Or.inl (by decide)),joint_residual 1248 (Or.inr (by decide)) (Or.inr (by decide)),
    joint_residual 163 (Or.inl (by decide)) (Or.inl (by decide)),joint_residual 64 (Or.inl (by decide)) (Or.inl (by decide)),
    joint_residual 96 (Or.inl (by decide)) (Or.inl (by decide))]
  exact ⟨mixed_residual_padding.2.2.2.1,mixed_residual_padding.2.2.2.2.1,mixed_residual_padding.1,rfl,rfl⟩

theorem joint_prefix_error : (twoHeapPut 3 (.struct (l := .memory) allChangedFields) 0
    (dynamicMemberData mixedLayout (.bytes .memory) 2 jointValues)).run mixedState =
    (.error (.stuck "memory write type"),allChangedState) :=
  twoHeapPut_second_error mixedState 3 _ 0 _ (by rfl) (by decide)

end Solidity.Yul.Views.Controls
