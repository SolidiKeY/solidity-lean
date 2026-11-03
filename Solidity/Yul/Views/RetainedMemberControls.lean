import Solidity.Yul.Views.RetainedMemberArray
import Solidity.Yul.Views.MemberArrayControls

namespace Solidity.Yul.Views.Controls

def retainedRefOld (_ : Fin 2) : Source.Val mixedLayout (.bytes .memory) := .memRef rfl 0
def retainedRefZeroPhysical := mstore mixedPhysical 1152 0
def retainedRefZeroHeap := mixedHeap.write 4 (dynamicMemberData mixedLayout (.bytes .memory) 0 Fin.elim0) (by rfl)
def retainedRefZeroState := withSourceHeap mixedState retainedRefZeroHeap

theorem retained_ref_zero_step : retainedMemberArrayHeap mixedHeap mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries
    4 (.bytes .memory) 2 retainedRefOld rfl retainedRefZeroPhysical = some retainedRefZeroHeap := by
  unfold retainedMemberArrayHeap
  rw [show mixedPlacement.address 4 = 1152 from rfl, show mload retainedRefZeroPhysical 1152 = 0 from mload_mstore _ _ _]
  rfl

def retainedRefZeroPlacement := retainedMemberArrayPlacement mixedPlacement mixedPlacement (retainInitial _ _) 4 (.bytes .memory) 2 retainedRefOld rfl 0 Fin.elim0 (by decide)
def retainedRefZeroHistory := retainedMemberArray_history mixedPlacement mixedPlacement (retainInitial _ _) 4 (.bytes .memory) 2 retainedRefOld rfl 0 Fin.elim0 (by decide)
def retainedRefZeroEntries : List (MixedHeapEntry retainedRefZeroPlacement) :=
  [⟨0, _, .bytes mixedChild, rfl, .bytes _ (by decide)⟩, ⟨1, _, .string mixedString, rfl, .string _ (by decide)⟩]
def retainedRefRegrowPhysical := mstore retainedRefZeroPhysical 1152 2

theorem retained_ref_tail (i : Fin 2) : mload retainedRefRegrowPhysical (1184 + i.val * 32) = 128 := by
  have outside : mload retainedRefRegrowPhysical (1184 + i.val * 32) = mload mixedPhysical (1184 + i.val * 32) := by
    apply mload_congr
    intro j
    change mstore (mstore mixedPhysical 1152 0) 1152 2 (1184 + i.val * 32 + j.val) = _
    rw [mstore_outside _ _ _ _ (by omega), mstore_outside _ _ _ _ (by omega)]
  rw [outside]
  have choices : i = 0 ∨ i = 1 := by have hi := i.isLt; apply Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h); omega
  rcases choices with eq | eq
  · subst i; decide
  · subst i; decide

theorem retained_ref_regrow_decode : decodeArrayMembers retainedRefZeroPlacement retainedRefZeroEntries (.bytes .memory) 2 retainedRefRegrowPhysical 1184 = some retainedRefOld := by
  apply decodeArrayMembers_of_decodes
  intro i
  rw [retained_ref_tail]
  rfl

def retainedRefRegrowHeap := retainedRefZeroHeap.write 4 (dynamicMemberData mixedLayout (.bytes .memory) 2 retainedRefOld) (by rfl)
def retainedRefRegrowState := withSourceHeap retainedRefZeroState retainedRefRegrowHeap

theorem retained_ref_regrow_step : retainedMemberArrayHeap retainedRefZeroHeap mixedPlacement retainedRefZeroPlacement retainedRefZeroHistory retainedRefZeroEntries
    4 (.bytes .memory) 0 Fin.elim0 rfl retainedRefRegrowPhysical = some retainedRefRegrowHeap := by
  unfold retainedMemberArrayHeap
  rw [show retainedRefZeroPlacement.address 4 = 1152 from rfl, show mload retainedRefRegrowPhysical 1152 = 2 from mload_mstore _ _ _]
  rw [if_pos (by decide)]
  change (decodeArrayMembers retainedRefZeroPlacement retainedRefZeroEntries (.bytes .memory) 2 retainedRefRegrowPhysical 1184).map _ = _
  rw [retained_ref_regrow_decode]
  rfl

theorem retained_ref_source_zero : retainedMemberArrayState mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries 4 (.bytes .memory) retainedRefZeroPhysical =
    some (.ok (), retainedRefZeroState) := by
  unfold retainedMemberArrayState
  rw [show mixedPlacement.address 4 = 1152 from rfl, show mload retainedRefZeroPhysical 1152 = 0 from mload_mstore _ _ _]
  rfl

theorem retained_ref_source_regrow : retainedMemberArrayState retainedRefZeroState mixedPlacement retainedRefZeroPlacement retainedRefZeroHistory retainedRefZeroEntries 4 (.bytes .memory) retainedRefRegrowPhysical =
    some (.ok (), retainedRefRegrowState) := by
  unfold retainedMemberArrayState
  rw [show retainedRefZeroPlacement.address 4 = 1152 from rfl, show mload retainedRefRegrowPhysical 1152 = 2 from mload_mstore _ _ _]
  rw [if_pos (by decide)]
  change (decodeArrayMembers retainedRefZeroPlacement retainedRefZeroEntries (.bytes .memory) 2 retainedRefRegrowPhysical 1184).map _ = _
  rw [retained_ref_regrow_decode]
  rfl

theorem retained_ref_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H retainedRefRegrowState :=
  retainedMemberArray_MemOK mixedEnv H retainedRefZeroState mixedPlacement retainedRefZeroPlacement retainedRefZeroHistory retainedRefZeroEntries 4 (.bytes .memory) retainedRefRegrowPhysical _ retained_ref_source_regrow
    (retainedMemberArray_MemOK mixedEnv H mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries 4 (.bytes .memory) retainedRefZeroPhysical _ retained_ref_source_zero ok)

theorem retained_ref_aliases (horizon : Nat) :
    (readDynamicArrayBytes 0 horizon).run retainedRefRegrowState = (.ok mixedChild, retainedRefRegrowState) ∧
    (readDynamicArrayBytes 1 horizon).run retainedRefRegrowState = (.ok mixedChild, retainedRefRegrowState) ∧
    retainedRefRegrowHeap.get 0 = mixedHeap.get 0 ∧ retainedRefRegrowHeap.get 1 = mixedHeap.get 1 := ⟨rfl, rfl, rfl, rfl⟩

theorem retained_ref_old_guard : memberArrayStateWriteback retainedRefZeroState retainedRefZeroPlacement retainedRefZeroEntries 4 (.bytes .memory) none 0 (fun _ e => nomatch e) retainedRefRegrowPhysical = none := by
  unfold memberArrayStateWriteback
  rw [show retainedRefZeroPlacement.address 4 = 1152 from rfl]
  simp only [arrayLengthChoice, Option.getD_none, show mload retainedRefRegrowPhysical 1152 = 2 from mload_mstore _ _ _]
  rfl

theorem retained_ref_current_shape_and_history : retainedRefZeroPlacement.shape 4 = .array true 0 ∧ RetainedAllocation mixedPlacement retainedRefZeroPlacement :=
  ⟨rfl, retainedRefZeroHistory⟩

theorem retained_ref_beyond_original : retainedMemberArrayHeap retainedRefZeroHeap mixedPlacement retainedRefZeroPlacement retainedRefZeroHistory retainedRefZeroEntries 4 (.bytes .memory) 0 Fin.elim0 rfl (mstore retainedRefZeroPhysical 1152 3) = none := by
  unfold retainedMemberArrayHeap
  rw [show retainedRefZeroPlacement.address 4 = 1152 from rfl, mload_mstore]
  rfl

def boolDynTy : Source.STy := .array .memory .bool none
def boolDynHeap : Source.Heap mixedLayout := (Source.Heap.empty.alloc ⟨boolDynTy, dynamicMemberData mixedLayout .bool 3 boolOld⟩).1
def boolDynPlacement : Placement boolDynHeap where
  address a := 128 + a * 256
  shape _ := .array true 3
  free := 256
  free_start := by decide
  distinct a b _ _ same := by omega
  typed a τ d found := by
    cases a with
    | zero => cases found; exact .array _ _ _
    | succ a =>
      have absent := boolDynHeap.bounded (a + 1) (by change 1 ≤ a + 1; omega)
      change boolDynHeap.cells (a + 1) = some ⟨τ, d⟩ at found
      rw [absent] at found
      cases found
  starts a _ := by omega
  ends a present := by
    have zero : a = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro no
      have absent := boolDynHeap.bounded a no
      rw [absent] at present
      cases present
    subst a
    decide
  separate a b ha hb different := by
    have zero (i : Nat) (hi : (boolDynHeap.cells i).isSome) : i = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro no
      have absent := boolDynHeap.bounded i no
      rw [absent] at hi
      cases hi
    exact False.elim (different ((zero a ha).trans (zero b hb).symm))


def boolDynResidual : ByteView := mstore (mstore (fun _ => 0xa5) 64 256) 96 0
def boolDynPhysical := dynamicUintView 3 (by decide) boolOldWords boolDynResidual 128
def boolDynZeroPhysical := mstore boolDynPhysical 128 0
def boolDynZeroHeap := boolDynHeap.write 0 (dynamicMemberData mixedLayout .bool 0 Fin.elim0) (by rfl)
def boolDynZeroPlacement := retainedMemberArrayPlacement boolDynPlacement boolDynPlacement (retainInitial _ _) 0 .bool 3 boolOld rfl 0 Fin.elim0 (by decide)
def boolDynZeroHistory := retainedMemberArray_history boolDynPlacement boolDynPlacement (retainInitial _ _) 0 .bool 3 boolOld rfl 0 Fin.elim0 (by decide)
def boolDynRegrowPhysical := mstore boolDynZeroPhysical 128 3

theorem retained_bool_decode : decodeArrayMembers boolDynZeroPlacement [] .bool 3 boolDynRegrowPhysical 160 = some boolOld := by
  apply decodeArrayMembers_of_decodes
  intro i
  have read : mload boolDynRegrowPhysical (160 + i.val * 32) = boolOldWords i := by
    have eq : mload boolDynRegrowPhysical (160 + i.val * 32) = mload boolDynPhysical (160 + i.val * 32) := by
      apply mload_congr
      intro j
      change mstore (mstore boolDynPhysical 128 0) 128 3 (160 + i.val * 32 + j.val) = _
      rw [mstore_outside _ _ _ _ (by omega), mstore_outside _ _ _ _ (by omega)]
    rw [eq]
    exact dynamicUint_element _ _ _ _ _ i
  rw [read]
  unfold boolOldWords boolOld
  split <;> rfl

def boolDynState : Source.EMState mixedEnv [boolDynTy, boolDynTy] :=
  ⟨.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil), { mixedState.2 with heap := boolDynHeap }⟩
def boolDynZeroState := withSourceHeap boolDynState boolDynZeroHeap
def boolDynRegrowHeap := boolDynZeroHeap.write 0 (dynamicMemberData mixedLayout .bool 3 boolOld) (by rfl)
def boolDynRegrowState := withSourceHeap boolDynZeroState boolDynRegrowHeap

theorem retained_bool_zero : retainedMemberArrayState boolDynState boolDynPlacement boolDynPlacement (retainInitial _ _) [] 0 .bool boolDynZeroPhysical = some (.ok (), boolDynZeroState) := by
  unfold retainedMemberArrayState
  rw [show boolDynPlacement.address 0 = 128 from rfl, show mload boolDynZeroPhysical 128 = 0 from mload_mstore _ _ _]
  rfl

theorem retained_bool_regrow : retainedMemberArrayState boolDynZeroState boolDynPlacement boolDynZeroPlacement boolDynZeroHistory [] 0 .bool boolDynRegrowPhysical = some (.ok (), boolDynRegrowState) := by
  unfold retainedMemberArrayState
  rw [show boolDynZeroPlacement.address 0 = 128 from rfl, show mload boolDynRegrowPhysical 128 = 3 from mload_mstore _ _ _]
  rw [if_pos (by decide)]
  change (decodeArrayMembers boolDynZeroPlacement [] .bool 3 boolDynRegrowPhysical 160).map _ = _
  rw [retained_bool_decode]
  rfl

theorem retained_bool_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H boolDynState) : Source.MemOK mixedEnv H boolDynRegrowState :=
  retainedMemberArray_MemOK mixedEnv H boolDynZeroState boolDynPlacement boolDynZeroPlacement boolDynZeroHistory [] 0 .bool boolDynRegrowPhysical _ retained_bool_regrow
    (retainedMemberArray_MemOK mixedEnv H boolDynState boolDynPlacement boolDynPlacement (retainInitial _ _) [] 0 .bool boolDynZeroPhysical _ retained_bool_zero ok)

def boolDynEntry : MixedHeapEntry boolDynPlacement := ⟨0, _, dynamicMemberData mixedLayout .bool 3 boolOld, rfl,
  .words _ _ (.array (n := none) 3 (fun _ e => nomatch e) (by decide) boolOld boolOldWords (fun i => by
    unfold boolOld boolOldWords
    split <;> exact .scalar _ _ rfl))⟩

theorem retained_bool_initial_MemOK : Source.MemOK mixedEnv boolDynHeap.ty boolDynState := by
  have coverage : CoversMixedHeap [boolDynEntry] := by
    intro a present
    have zero : a = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro no
      have absent := boolDynHeap.bounded a no
      rw [absent] at present
      cases present
    subst a
    exact ⟨boolDynEntry, List.mem_cons_self, rfl⟩
  obtain ⟨heap, top, inner⟩ := mixedHeap_owner_invariants boolDynPlacement [boolDynEntry] coverage
  exact ⟨⟨⟨heap, Source.HeapTy.Le.refl _⟩, ⟨⟨boolDynTy, rfl, rfl⟩, ⟨⟨boolDynTy, rfl, rfl⟩, trivial⟩⟩⟩, top, inner⟩

theorem retained_bool_alias_lengths :
    (Source.lengthOf mixedReadFrame (boolDynZeroState.1.get .here)).run boolDynZeroState = (.ok 0, boolDynZeroState) ∧
    (Source.lengthOf mixedReadFrame (boolDynRegrowState.1.get .here)).run boolDynRegrowState = (.ok 3, boolDynRegrowState) ∧
    (Source.lengthOf mixedReadFrame (boolDynRegrowState.1.get (.there .here))).run boolDynRegrowState = (.ok 3, boolDynRegrowState) ∧
    (Source.readLoc (E := mixedEnv) mixedReadFrame (τ := .bool) (.mem 0 1)).run boolDynRegrowState = (.ok (.bool true), boolDynRegrowState) := ⟨rfl, rfl, rfl, rfl⟩

theorem retained_member_source_error : retainedMemberArrayState mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries 0 (.bytes .memory)
    (mstore mixedPhysical 128 0) = some (.error (.stuck "memory write type"), mixedState) := by
  unfold retainedMemberArrayState
  rw [show mixedPlacement.address 0 = 128 from rfl, mload_mstore]
  rfl

theorem retained_member_disjoint_source_orders :
    retainedRefZeroHeap.write 0 (.bytes ([] : List UInt8)) (by rfl) =
      (mixedHeap.write 0 (.bytes ([] : List UInt8)) (by rfl)).write 4 (dynamicMemberData mixedLayout (.bytes .memory) 0 Fin.elim0) (by rfl) :=
  heap_writes_commute mixedHeap 4 0 _ _ rfl rfl (by decide)

theorem retained_member_disjoint_physical_orders : mstore (mstore mixedPhysical 1152 0) 128 0 = mstore (mstore mixedPhysical 128 0) 1152 0 :=
  mstore_disjoint_commute mixedPhysical 1152 128 0 0 (Or.inr (by decide))

theorem retained_member_gaps_and_reserved : retainedRefRegrowPhysical 64 = mixedPhysical 64 ∧ retainedRefRegrowPhysical 96 = mixedPhysical 96 ∧
    retainedRefRegrowPhysical 1248 = mixedPhysical 1248 ∧ boolDynRegrowPhysical 64 = boolDynPhysical 64 ∧
    boolDynRegrowPhysical 96 = boolDynPhysical 96 ∧ boolDynRegrowPhysical 256 = boolDynPhysical 256 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact (mstore_outside _ _ _ _ (by decide)).trans (mstore_outside _ _ _ _ (by decide))

end Solidity.Yul.Views.Controls
