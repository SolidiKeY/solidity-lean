import Solidity.Yul.Views.StaticUintMemory
import Solidity.Yul.Views.PointerMemory
import Solidity.Yul.Views.MixedHeapControls

namespace Solidity.Yul.Views.Controls

def oldStaticWords (i : Fin 2) : Roadmap.Word := if i.val = 0 then 7 else 9
def changedStaticWords (i : Fin 2) : Roadmap.Word := if i.val = 0 then 7 else 42
def changedStaticPhysical := mstore mixedPhysical 672 42
def changedStaticHeap := mixedHeap.write 2 (staticUintData mixedLayout 2 changedStaticWords) (by rfl)
def changedStaticState := withSourceHeap mixedState changedStaticHeap

theorem old_static_data : staticUintData mixedLayout 2 oldStaticWords = mixedStatic := by
  apply congrArg (fun values : Fin 2 → Source.Data mixedLayout (.int Source.IntTy.u256) =>
    Source.Data.array (l := .memory) (n := some 2) 2 (fun _ e => (Option.some.inj e).symm) values)
  funext i
  unfold oldStaticWords mixedStaticVals
  split <;> rfl

theorem old_static_found : mixedHeap.get 2 = some ⟨_, staticUintData mixedLayout 2 oldStaticWords⟩ := by
  rw [old_static_data]
  rfl

theorem changed_static_decode : decodeStaticUint mixedLayout 2 changedStaticPhysical 640 = staticUintData mixedLayout 2 changedStaticWords := by
  apply congrArg (staticUintData mixedLayout 2)
  funext i
  have choices : i.val = 0 ∨ i.val = 1 := by have bound := i.isLt; omega
  rcases choices with eq | eq
  · have index : i = 0 := Fin.ext eq
    subst i
    change mload (mstore mixedPhysical 672 42) 640 = 7
    rw [mload_congr (mstore mixedPhysical 672 42) mixedPhysical 640
      (fun j => mstore_outside _ _ _ _ (by have hi := j.isLt; omega))]
    exact mixed_exact_words.2.2.1
  · have index : i = 1 := Fin.ext eq
    subst i
    exact mload_mstore mixedPhysical 672 42

theorem changed_static_writeback : staticUintWriteback mixedHeap mixedPlacement 2 2 oldStaticWords old_static_found changedStaticPhysical = changedStaticHeap := by
  unfold staticUintWriteback
  rw [show mixedPlacement.address 2 = 640 from rfl, changed_static_decode]
  rfl

theorem changed_static_state : staticUintStateWriteback mixedState mixedPlacement 2 2 oldStaticWords old_static_found changedStaticPhysical = changedStaticState := by
  change withSourceHeap mixedState (staticUintWriteback mixedHeap mixedPlacement 2 2 oldStaticWords old_static_found changedStaticPhysical) = _
  rw [changed_static_writeback]
  rfl

theorem changed_static_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) :
    Source.MemOK mixedEnv H changedStaticState := by
  rw [← changed_static_state]
  exact staticUintState_MemOK mixedEnv H mixedState mixedPlacement 2 2 oldStaticWords old_static_found _ ok

def staticAliasState : Source.EMState mixedEnv
    [.array .memory (.int Source.IntTy.u256) (some 2), .array .memory (.int Source.IntTy.u256) (some 2)] :=
  ⟨.cons (.memRef rfl 2) (.cons (.memRef rfl 2) .nil), mixedState.2⟩
def staticAliasAfter := withSourceHeap staticAliasState changedStaticHeap

theorem static_alias_initial_MemOK : Source.MemOK mixedEnv mixedHeap.ty staticAliasState := by
  refine ⟨⟨mixed_actual_MemOK.1.1, ?_⟩, mixed_actual_MemOK.2⟩
  exact ⟨⟨.array .memory (.int Source.IntTy.u256) (some 2), rfl, rfl⟩,
    ⟨⟨.array .memory (.int Source.IntTy.u256) (some 2), rfl, rfl⟩, trivial⟩⟩

theorem static_source_aliases : staticAliasAfter.1.get (.here) = .memRef rfl 2 ∧
    staticAliasAfter.1.get (.there .here) = .memRef rfl 2 ∧
    (Source.readLoc (E := mixedEnv) mixedReadFrame (τ := .int Source.IntTy.u256) (.mem 2 1)).run staticAliasAfter =
      (.ok (uintValueOfWord mixedLayout 42), staticAliasAfter) := ⟨rfl, rfl, rfl⟩

theorem static_other_roots : changedStaticHeap.get 0 = mixedHeap.get 0 ∧ changedStaticHeap.get 3 = mixedHeap.get 3 ∧
    changedStaticHeap.get 4 = mixedHeap.get 4 ∧ changedStaticHeap.get 5 = mixedHeap.get 5 := ⟨rfl, rfl, rfl, rfl⟩

theorem static_unmodified_identity : staticUintWriteback mixedHeap mixedPlacement 2 2 oldStaticWords old_static_found mixedPhysical = mixedHeap := by
  apply staticUintWriteback_unchanged
  intro i
  have choices : i.val = 0 ∨ i.val = 1 := by have bound := i.isLt; omega
  rcases choices with eq | eq
  · have index : i = 0 := Fin.ext eq
    subst i
    exact mixed_exact_words.2.2.1
  · have index : i = 1 := Fin.ext eq
    subst i
    exact mixed_exact_words.2.2.2.1

def highestUint : Roadmap.Word := ⟨2 ^ 256 - 1, by decide⟩
theorem static_all_bits_retained : (uintValueOfWord mixedLayout highestUint).word = some highestUint := uintValueOfWord_word _ _

def retargetFields : Source.DataList mixedLayout (mixedLayout.fields mixedName) :=
  .cons (.val (.bool true)) (.cons (.val mixedSeven) (.cons (.val (.memRef rfl 0))
    (.cons (.val (.memRef rfl 1)) (.cons (.val (.memRef rfl 4)) .nil))))
def retargetHeap := mixedHeap.write 3 (.struct retargetFields) (by rfl)
def retargetState := withSourceHeap mixedState retargetHeap

theorem pointer_decode_owned : decodeMemoryPointer mixedPlacement mixedEntries (.bytes .memory) rfl 128 = some (.memRef rfl 0) :=
  decodeMemoryPointer_encode _ _ mixed_coverage _ rfl 0 (.bytes .memory) rfl rfl

theorem pointer_decode_string_alias : decodeMemoryPointer mixedPlacement mixedEntries (.bytes .memory) rfl 384 = some (.memRef rfl 1) :=
  decodeMemoryPointer_encode _ _ mixed_coverage _ rfl 1 (.string .memory) rfl rfl

theorem pointer_wrong_bits_none : decodeMemoryPointer mixedPlacement mixedEntries (.bytes .memory) rfl 129 = none := rfl

theorem pointer_missing_type_none : decodeMemoryPointer mixedPlacement mixedEntries (.bytes .memory) rfl 640 = none := rfl

theorem pointer_shared_zero_still_open : decodeMemoryPointer mixedPlacement mixedEntries (.bytes .memory) rfl 96 = none := rfl

theorem pointer_missing_coverage_not_support : decodeMemoryPointer mixedPlacement [] (.bytes .memory) rfl 128 = none := rfl

theorem retarget_source_step (horizon : Nat) : pointerStateWriteback mixedState mixedPlacement mixedEntries mixedReadFrame horizon
    3 3 (.bytes .memory) rfl 384 = some (.ok (), retargetState) := by
  unfold pointerStateWriteback
  rw [pointer_decode_string_alias]
  rfl

theorem retarget_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) (horizon : Nat) :
    Source.MemOK mixedEnv H retargetState :=
  pointerStateWriteback_MemOK mixedEnv H _ _ _ mixedReadFrame horizon 3 3 _ rfl 384 (.ok (), retargetState)
    (retarget_source_step horizon) ok

def readMixedMemberBytes (member horizon : Nat) : Source.EM mixedEnv
    [.bytes .memory, .string .memory, mixedArrayTy, .struct .memory mixedName] (List UInt8) := do
  let pointer ← Source.readLoc mixedReadFrame (τ := .bytes .memory) (.mem 3 member)
  Source.bytesOfRV mixedReadFrame horizon (.val pointer)

theorem retarget_actual_aliases (horizon : Nat) :
    (readMixedMemberBytes 2 horizon).run retargetState = (.ok mixedChild, retargetState) ∧
    (readMixedMemberBytes 3 horizon).run retargetState = (.ok mixedString, retargetState) ∧
    retargetHeap.get 0 = mixedHeap.get 0 ∧ retargetHeap.get 1 = mixedHeap.get 1 ∧ retargetHeap.next = mixedHeap.next := ⟨rfl, rfl, rfl, rfl, rfl⟩

def retargetPhysical := mstore mixedPhysical 992 384

theorem retarget_physical_source_step (horizon : Nat) : structPointerWriteback mixedState mixedPlacement mixedEntries mixedReadFrame horizon
    3 mixedName mixedFields rfl ⟨3, by decide⟩ (.bytes .memory) rfl rfl retargetPhysical = some (.ok (), retargetState) := by
  unfold structPointerWriteback
  change pointerStateWriteback mixedState mixedPlacement mixedEntries mixedReadFrame horizon 3 3 (.bytes .memory) rfl (mload (mstore mixedPhysical 992 384) 992) = _
  rw [mload_mstore]
  exact retarget_source_step horizon

theorem retarget_unchanged_source_step (horizon : Nat) : pointerStateWriteback mixedState mixedPlacement mixedEntries mixedReadFrame horizon
    3 3 (.bytes .memory) rfl 128 = some (.ok (), mixedState) := by
  unfold pointerStateWriteback
  rw [pointer_decode_owned]
  change some ((.ok () : Except Source.Halt Unit), withSourceHeap mixedState (mixedHeap.write 3 mixedStruct (by rfl))) = some ((.ok () : Except Source.Halt Unit), mixedState)
  rw [heap_write_unchanged mixedHeap 3 _ mixedStruct (by rfl)]
  rfl

theorem retarget_failure_leaves_state : pointerStateWriteback mixedState mixedPlacement mixedEntries mixedReadFrame 0
    3 3 (.bytes .memory) rfl 129 = none := by
  unfold pointerStateWriteback
  rw [pointer_wrong_bits_none]
  rfl

theorem static_raw_reencode : wordListView (List.ofFn (fun i : Fin 2 => mload changedStaticPhysical (640 + i.val * 32))) changedStaticPhysical 640 = changedStaticPhysical :=
  decodeStaticUint_reencode 2 _ 640

theorem component_physical_residual : retargetPhysical 163 = mixedPhysical 163 ∧
    retargetPhysical 1056 = mixedPhysical 1056 ∧ changedStaticPhysical 704 = mixedPhysical 704 ∧
    retargetPhysical 64 = mixedPhysical 64 ∧ changedStaticPhysical 96 = mixedPhysical 96 := by
  exact ⟨mstore_outside _ _ _ _ (by decide), mstore_outside _ _ _ _ (by decide),
    mstore_outside _ _ _ _ (by decide), mstore_outside _ _ _ _ (by decide), mstore_outside _ _ _ _ (by decide)⟩

def combinedWordHeap := changedStaticHeap.write 3 (.struct retargetFields) (by rfl)

theorem disjoint_word_source_writes : combinedWordHeap = retargetHeap.write 2 (staticUintData mixedLayout 2 changedStaticWords) (by rfl) :=
  heap_writes_commute mixedHeap 2 3 _ _ rfl rfl (by decide)

theorem component_reserved : ReservedOK changedStaticPhysical 1664 ∧ ReservedOK retargetPhysical 1664 :=
  ⟨mstore_object_header_reserved mixedPhysical 672 42 1664 (by decide) mixed_reserved,
   mstore_object_header_reserved mixedPhysical 992 384 1664 (by decide) mixed_reserved⟩

def changedStaticPlacement : Placement changedStaticHeap := heapWritePlacement mixedHeap mixedPlacement 2
  (staticUintData mixedLayout 2 changedStaticWords) (by rfl) (.array 2 _ _)
def pointerAfterStaticEntries : List (MixedHeapEntry changedStaticPlacement) :=
  [⟨1, .string .memory, .string mixedString, rfl, .string mixedString (by decide)⟩]
def combinedWordState := withSourceHeap mixedState combinedWordHeap

theorem array_then_pointer_source (horizon : Nat) : pointerStateWriteback changedStaticState changedStaticPlacement pointerAfterStaticEntries
    mixedReadFrame horizon 3 3 (.bytes .memory) rfl 384 = some (.ok (), combinedWordState) := rfl

theorem combined_word_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) (horizon : Nat) :
    Source.MemOK mixedEnv H combinedWordState :=
  pointerStateWriteback_MemOK mixedEnv H _ _ _ mixedReadFrame horizon 3 3 _ rfl 384 (.ok (), combinedWordState)
    (array_then_pointer_source horizon) (changed_static_MemOK H ok)

def retargetPlacement : Placement retargetHeap := heapWritePlacement mixedHeap mixedPlacement 3 (.struct retargetFields) (by rfl) (.strct _)
def reverseWordPhysical := mstore retargetPhysical 672 42

theorem pointer_then_array_source : staticUintStateWriteback retargetState retargetPlacement 2 2 oldStaticWords
    (by change retargetHeap.get 2 = some ⟨_, staticUintData mixedLayout 2 oldStaticWords⟩; rw [old_static_data]; rfl) reverseWordPhysical = combinedWordState := by
  have words : (fun i : Fin 2 => mload reverseWordPhysical (retargetPlacement.address 2 + i.val * 32)) = changedStaticWords := by
    funext i
    have choices : i.val = 0 ∨ i.val = 1 := by have bound := i.isLt; omega
    rcases choices with eq | eq
    · have index : i = 0 := Fin.ext eq
      subst i
      change mload (mstore (mstore mixedPhysical 992 384) 672 42) 640 = 7
      rw [mload_congr _ (mstore mixedPhysical 992 384) 640 (fun j => mstore_outside _ _ _ _ (by have hi := j.isLt; omega)),
        mload_congr _ mixedPhysical 640 (fun j => mstore_outside _ _ _ _ (by have hi := j.isLt; omega))]
      exact mixed_exact_words.2.2.1
    · have index : i = 1 := Fin.ext eq
      subst i
      exact mload_mstore retargetPhysical 672 42
  unfold staticUintStateWriteback staticUintWriteback decodeStaticUint
  change withSourceHeap retargetState (retargetHeap.write 2 (staticUintData mixedLayout 2 _) _) = _
  rw [words, ← disjoint_word_source_writes]
  rfl

def combinedWordPhysical := mstore changedStaticPhysical 992 384

theorem disjoint_word_physical_orders : combinedWordPhysical = reverseWordPhysical :=
  mstore_disjoint_commute mixedPhysical 672 992 42 384 (Or.inl (by decide))

theorem array_then_physical_pointer (horizon : Nat) : structPointerWriteback changedStaticState changedStaticPlacement pointerAfterStaticEntries
    mixedReadFrame horizon 3 mixedName mixedFields rfl ⟨3, by decide⟩ (.bytes .memory) rfl rfl combinedWordPhysical = some (.ok (), combinedWordState) := by
  unfold structPointerWriteback
  change pointerStateWriteback changedStaticState changedStaticPlacement pointerAfterStaticEntries mixedReadFrame horizon 3 3
    (.bytes .memory) rfl (mload (mstore changedStaticPhysical 992 384) 992) = _
  rw [mload_mstore]
  exact array_then_pointer_source horizon

#print axioms disjoint_word_physical_orders
#print axioms array_then_physical_pointer
#print axioms combined_word_MemOK
#print axioms pointer_then_array_source
#print axioms retarget_physical_source_step
#print axioms retarget_unchanged_source_step
#print axioms disjoint_word_source_writes
#print axioms changed_static_writeback
#print axioms changed_static_MemOK
#print axioms retarget_source_step
#print axioms retarget_MemOK
#print axioms retarget_actual_aliases
end Solidity.Yul.Views.Controls
