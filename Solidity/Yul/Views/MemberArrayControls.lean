import Solidity.Yul.Views.MemberArray
import Solidity.Yul.Views.DynamicUintControls

namespace Solidity.Yul.Views.Controls

def boolArrayTy : Source.STy := .array .memory .bool (some 3)
def boolOld (i : Fin 3) : Source.Val mixedLayout .bool := if i.val = 1 then .bool true else .bool false
def boolNew (i : Fin 3) : Source.Val mixedLayout .bool := if i.val = 1 then .bool false else .bool true
def boolOldWords (i : Fin 3) : Roadmap.Word := if i.val = 1 then 1 else 0
def boolNewWords (i : Fin 3) : Roadmap.Word := if i.val = 1 then 0 else 1
def boolLength : ∀ x, some 3 = some x → x = 3 := fun _ e => (Option.some.inj e).symm
def boolHeap : Source.Heap mixedLayout := (Source.Heap.empty.alloc ⟨boolArrayTy, memberArrayData mixedLayout .bool (some 3) 3 boolLength boolOld⟩).1

def boolPlacement : Placement boolHeap where
  address a := 128 + a * 256
  shape _ := .array false 3
  free := 224
  free_start := by decide
  distinct a b _ _ same := by omega
  typed a τ d found := by
    cases a with
    | zero => cases found; exact .array _ _ _
    | succ a =>
      have absent := boolHeap.bounded (a + 1) (by change 1 ≤ a + 1; omega)
      change boolHeap.cells (a + 1) = some ⟨τ, d⟩ at found
      rw [absent] at found
      cases found
  starts a _ := by omega
  ends a present := by
    have zero : a = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro no
      have absent := boolHeap.bounded a no
      rw [absent] at present
      cases present
    subst a
    decide
  separate a b ha hb different := by
    have zero (i : Nat) (hi : (boolHeap.cells i).isSome) : i = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro no
      have absent := boolHeap.bounded i no
      rw [absent] at hi
      cases hi
    exact False.elim (different ((zero a ha).trans (zero b hb).symm))

theorem bool_old_encoding (i : Fin 3) : MemoryElement boolPlacement (boolOld i) (boolOldWords i) := by
  unfold boolOld boolOldWords
  split <;> exact .scalar _ _ rfl

theorem bool_new_encoding (i : Fin 3) : MemoryElement boolPlacement (boolNew i) (boolNewWords i) := by
  unfold boolNew boolNewWords
  split <;> exact .scalar _ _ rfl

def boolEntry : MixedHeapEntry boolPlacement := ⟨0, _, memberArrayData mixedLayout .bool (some 3) 3 boolLength boolOld, rfl,
  .words _ _ (.array 3 boolLength (by decide) boolOld boolOldWords bool_old_encoding)⟩

theorem bool_coverage : CoversMixedHeap [boolEntry] := by
  intro a ha
  have zero : a = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro no
    have absent := boolHeap.bounded a no
    rw [absent] at ha
    cases ha
  subst a
  exact ⟨boolEntry, List.mem_cons_self, rfl⟩

def boolResidual : ByteView := mstore (mstore (fun _ => 0xa5) 64 224) 96 0
def boolPhysical := memberArrayView (some 3) 3 (by decide) boolOldWords boolResidual 128
def boolChangedPhysical := memberArrayView (some 3) 3 (by decide) boolNewWords boolPhysical 128
def boolChangedHeap := boolHeap.write 0 (memberArrayData mixedLayout .bool (some 3) 3 boolLength boolNew) (by rfl)
def boolState : Source.EMState mixedEnv [boolArrayTy, boolArrayTy] :=
  ⟨.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil), { mixedState.2 with heap := boolHeap }⟩
def boolChangedState := withSourceHeap boolState boolChangedHeap

theorem bool_actual_MemOK : Source.MemOK mixedEnv boolHeap.ty boolState := by
  obtain ⟨heap, top, inner⟩ := mixedHeap_owner_invariants boolPlacement [boolEntry] bool_coverage
  exact ⟨⟨⟨heap, Source.HeapTy.Le.refl _⟩, ⟨⟨boolArrayTy, rfl, rfl⟩, ⟨⟨boolArrayTy, rfl, rfl⟩, trivial⟩⟩⟩, top, inner⟩

theorem bool_changed_decode : decodeArrayMembers boolPlacement [boolEntry] .bool 3 boolChangedPhysical 128 = some boolNew :=
  decodeArrayMembers_encode boolPlacement [boolEntry] bool_coverage .bool (Or.inl rfl) 3 boolNew boolNewWords bool_new_encoding boolPhysical 128

theorem bool_changed_source : memberArrayStateWriteback boolState boolPlacement [boolEntry] 0 .bool (some 3) 3 boolLength boolChangedPhysical = some (.ok (), boolChangedState) := by
  unfold memberArrayStateWriteback
  simp only [arrayLengthChoice, Option.getD_some, if_true]
  change (decodeArrayMembers boolPlacement [boolEntry] .bool 3 boolChangedPhysical 128).map _ = _
  rw [bool_changed_decode]
  rfl

theorem bool_changed_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H boolState) : Source.MemOK mixedEnv H boolChangedState :=
  memberArrayState_MemOK mixedEnv H boolState boolPlacement [boolEntry] 0 .bool (some 3) 3 boolLength boolChangedPhysical _ bool_changed_source ok

theorem bool_unchanged_whole_state : memberArrayStateWriteback boolState boolPlacement [boolEntry] 0 .bool (some 3) 3 boolLength boolPhysical = some (.ok (), boolState) := by
  apply memberArrayState_unchanged boolState boolPlacement [boolEntry] bool_coverage 0 .bool (Or.inl rfl) (some 3) 3 boolLength boolOld rfl boolOldWords bool_old_encoding boolPhysical rfl
  exact memberArrayView_element (some 3) 3 (by decide) boolOldWords boolResidual 128

theorem bool_alias_reads : boolChangedState.1.get .here = .memRef rfl 0 ∧ boolChangedState.1.get (.there .here) = .memRef rfl 0 ∧
    (Source.readLoc (E := mixedEnv) mixedReadFrame (τ := .bool) (.mem 0 2)).run boolChangedState = (.ok (.bool true), boolChangedState) := ⟨rfl, rfl, rfl⟩

def arrayRefOld (_ : Fin 2) : Source.Val mixedLayout dynTy := .memRef rfl 0
def arrayRefNew (_ : Fin 2) : Source.Val mixedLayout dynTy := .memRef rfl 1
def arrayRefLength : ∀ x, some 2 = some x → x = 2 := fun _ e => (Option.some.inj e).symm

theorem array_ref_new_encoding (i : Fin 2) : MemoryElement dynPlacement (arrayRefNew i) 384 :=
  .pointer rfl 1 dynTy rfl rfl

def arrayRefPhysical := memberArrayView (some 2) 2 (by decide) (fun _ => 384) dynPhysical 896
def arrayRefHeap := dynHeap.write 3 (memberArrayData mixedLayout dynTy (some 2) 2 arrayRefLength arrayRefNew) (by rfl)
def arrayRefState := withSourceHeap dynState arrayRefHeap

theorem array_ref_source : memberArrayStateWriteback dynState dynPlacement dynEntries 3 dynTy (some 2) 2 arrayRefLength arrayRefPhysical = some (.ok (), arrayRefState) := by
  have decode : decodeArrayMembers dynPlacement dynEntries dynTy 2 arrayRefPhysical 896 = some arrayRefNew := decodeArrayMembers_encode dynPlacement dynEntries dyn_coverage dynTy (Or.inr (Or.inr rfl)) 2 arrayRefNew (fun _ => 384) array_ref_new_encoding dynPhysical 896
  unfold memberArrayStateWriteback
  simp only [arrayLengthChoice, Option.getD_some, if_true]
  change (decodeArrayMembers dynPlacement dynEntries dynTy 2 arrayRefPhysical 896).map _ = _
  rw [decode]
  rfl

theorem array_ref_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H dynState) : Source.MemOK mixedEnv H arrayRefState :=
  memberArrayState_MemOK mixedEnv H dynState dynPlacement dynEntries 3 dynTy (some 2) 2 arrayRefLength arrayRefPhysical _ array_ref_source ok

def readArrayAliasLength (i : Nat) : Source.EM mixedEnv [dynTy, dynTy] Nat := do
  let ref ← Source.readLoc mixedReadFrame (τ := dynTy) (.mem 3 i)
  Source.lengthOf mixedReadFrame ref

theorem array_ref_nested_aliases : (readArrayAliasLength 0).run arrayRefState = (.ok 2, arrayRefState) ∧
    (readArrayAliasLength 1).run arrayRefState = (.ok 2, arrayRefState) ∧ arrayRefHeap.get 0 = dynHeap.get 0 ∧ arrayRefHeap.get 1 = dynHeap.get 1 := ⟨rfl, rfl, rfl, rfl⟩

def arraySharedHeap := arrayRefHeap.write 1 (dynamicUintData mixedLayout 2 dynChangedOther) (by rfl)
def arraySharedState := withSourceHeap arrayRefState arraySharedHeap

def readArrayAliasWord (i : Nat) : Source.EM mixedEnv [dynTy, dynTy] (Source.Val mixedLayout (.int Source.IntTy.u256)) := do
  let ref ← Source.readLoc mixedReadFrame (τ := dynTy) (.mem 3 i)
  let loc ← Source.indexLoc mixedReadFrame ref 0
  Source.readLoc mixedReadFrame loc

theorem array_shared_alias_reads : (readArrayAliasWord 0).run arraySharedState = (.ok (uintValueOfWord mixedLayout highestUint), arraySharedState) ∧
    (readArrayAliasWord 1).run arraySharedState = (.ok (uintValueOfWord mixedLayout highestUint), arraySharedState) := ⟨rfl, rfl⟩

theorem array_shared_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H dynState) : Source.MemOK mixedEnv H arraySharedState :=
  dynamicUint_write_MemOK mixedEnv H arrayRefState 1 2 dynChangedOther rfl (array_ref_MemOK H ok)

theorem array_disjoint_source_orders : arraySharedHeap =
    (dynHeap.write 1 (dynamicUintData mixedLayout 2 dynChangedOther) (by rfl)).write 3 (memberArrayData mixedLayout dynTy (some 2) 2 arrayRefLength arrayRefNew) (by rfl) :=
  heap_writes_commute dynHeap 3 1 _ _ rfl rfl (by decide)

def dynamicRefNew (_ : Fin 2) : Source.Val mixedLayout (.bytes .memory) := .memRef rfl 1
def dynamicRefPhysical := memberArrayView none 2 (by decide) (fun _ => 384) mixedPhysical 1152
def dynamicRefHeap := mixedHeap.write 4 (memberArrayData mixedLayout (.bytes .memory) none 2 (fun _ e => nomatch e) dynamicRefNew) (by rfl)
def dynamicRefState := withSourceHeap mixedState dynamicRefHeap

theorem dynamic_ref_source : memberArrayStateWriteback mixedState mixedPlacement mixedEntries 4 (.bytes .memory) none 2 (fun _ e => nomatch e) dynamicRefPhysical = some (.ok (), dynamicRefState) := by
  have header : arrayLengthChoice none dynamicRefPhysical 1152 = 2 := memberArrayView_length none 2 (fun _ e => nomatch e) (by decide) (fun _ => 384) mixedPhysical 1152
  have decoded := decodeArrayMembers_reads mixedPlacement mixedEntries mixed_coverage (.bytes .memory) (Or.inr (Or.inr rfl)) 2 dynamicRefNew (fun _ => 384)
    (fun _ => .pointer (τ := .bytes .memory) rfl 1 (.string .memory) rfl rfl) dynamicRefPhysical 1184
    (memberArrayView_element none 2 (by decide) (fun _ => 384) mixedPhysical 1152)
  unfold memberArrayStateWriteback
  rw [show mixedPlacement.address 4 = 1152 from rfl, if_pos header]
  change (decodeArrayMembers mixedPlacement mixedEntries (.bytes .memory) 2 dynamicRefPhysical 1184).map _ = _
  rw [decoded]
  rfl

theorem array_missing_candidates_not_support : decodeArrayMembers dynPlacement [] dynTy 2 arrayRefPhysical 896 = none := by
  have head : mload arrayRefPhysical 896 = 384 := memberArrayView_element (some 2) 2 (by decide) (fun _ => 384) dynPhysical 896 0
  simp only [decodeArrayMembers, head]
  rfl

theorem array_dirty_bool_not_support : decodeArrayMembers boolPlacement [boolEntry] .bool 3 (mstore boolPhysical 128 2) 128 = none := by
  simp only [decodeArrayMembers, mload_mstore]
  rfl

theorem array_source_type_error : memberArrayStateWriteback mixedState mixedPlacement mixedEntries 0 .bool (some 3) 3 boolLength
    (memberArrayView (some 3) 3 (by decide) boolNewWords mixedPhysical 128) = some (.error (.stuck "memory write type"), mixedState) := by
  have enc (i : Fin 3) : MemoryElement mixedPlacement (boolNew i) (boolNewWords i) := by
    unfold boolNew boolNewWords
    split <;> exact .scalar _ _ rfl
  have decoded : decodeArrayMembers mixedPlacement mixedEntries .bool 3 (memberArrayView (some 3) 3 (by decide) boolNewWords mixedPhysical 128) 128 = some boolNew := decodeArrayMembers_encode mixedPlacement mixedEntries mixed_coverage .bool (Or.inl rfl) 3 boolNew boolNewWords enc mixedPhysical 128
  unfold memberArrayStateWriteback
  simp only [arrayLengthChoice, Option.getD_some, if_true]
  change (decodeArrayMembers mixedPlacement mixedEntries .bool 3 (memberArrayView (some 3) 3 (by decide) boolNewWords mixedPhysical 128) 128).map _ = _
  rw [decoded]
  simp only [Option.map_some]
  rw [memberArrayHeapPut_error mixedState 0 .bool (some 3) 3 boolLength boolNew (by decide)]

def readDynamicArrayBytes (i horizon : Nat) : Source.EM mixedEnv
    [.bytes .memory, .string .memory, mixedArrayTy, .struct .memory mixedName] (List UInt8) := do
  let ref ← Source.readLoc mixedReadFrame (τ := .bytes .memory) (.mem 4 i)
  Source.bytesOfRV mixedReadFrame horizon (.val ref)

theorem dynamic_array_aliases_every_horizon (horizon : Nat) :
    (readDynamicArrayBytes 0 horizon).run dynamicRefState = (.ok mixedString, dynamicRefState) ∧
    (readDynamicArrayBytes 1 horizon).run dynamicRefState = (.ok mixedString, dynamicRefState) := ⟨rfl, rfl⟩

theorem member_disjoint_physical_orders :
    wordListView [384, 384] (dynamicUintView 2 (by decide) dynChangedOther dynPhysical 384) 896 =
    dynamicUintView 2 (by decide) dynChangedOther (wordListView [384, 384] dynPhysical 896) 384 :=
  wordList_disjoint_commute (2 :: List.ofFn dynChangedOther) [384, 384] dynPhysical 384 896 (Or.inl (by decide))

theorem member_reserved_gaps : boolChangedPhysical 64 = boolPhysical 64 ∧ boolChangedPhysical 96 = boolPhysical 96 ∧
    boolChangedPhysical 224 = 0xa5 ∧ arrayRefPhysical 64 = dynPhysical 64 ∧ arrayRefPhysical 960 = dynPhysical 960 := by
  refine ⟨memberArrayView_residual _ _ _ _ _ _ _ (Or.inl (by decide)),
    memberArrayView_residual _ _ _ _ _ _ _ (Or.inl (by decide)), ?_,
    memberArrayView_residual _ _ _ _ _ _ _ (Or.inl (by decide)), memberArrayView_residual _ _ _ _ _ _ _ (Or.inr (by decide))⟩
  unfold boolChangedPhysical
  rw [memberArrayView_residual _ _ _ _ _ _ _ (Or.inr (by decide))]
  unfold boolPhysical
  rw [memberArrayView_residual _ _ _ _ _ _ _ (Or.inr (by decide))]
  rfl

end Solidity.Yul.Views.Controls
