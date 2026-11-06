import Solidity.Yul.Views.RetainedDynamicUint
import Solidity.Yul.Views.WordWritebackControls

namespace Solidity.Yul.Views.Controls

def dynTy : Source.STy := .array .memory (.int Source.IntTy.u256) none
def dynWords (i : Fin 3) : Roadmap.Word := if i.val = 0 then 7 else if i.val = 1 then 9 else highestUint
def dynOther (i : Fin 2) : Roadmap.Word := if i.val = 0 then 11 else 13
def dynHeap : Source.Heap mixedLayout :=
  ((((Source.Heap.empty.alloc ⟨dynTy, dynamicUintData mixedLayout 3 dynWords⟩).1.alloc
    ⟨dynTy, dynamicUintData mixedLayout 2 dynOther⟩).1.alloc
    ⟨.bytes .memory, .bytes mixedOther⟩).1.alloc
    ⟨.array .memory dynTy (some 2), .array 2 (fun _ e => (Option.some.inj e).symm)
      (fun _ => .val (.memRef rfl 0))⟩).1

def dynShape (a : Nat) : MemoryShape := if a = 0 then .array true 3 else
  if a = 1 then .array true 2 else if a = 2 then .bytes 3 else .array false 2

def dynPlacement : Placement dynHeap where
  address a := 128 + a * 256
  shape := dynShape
  free := 1152
  free_start := by decide
  distinct a b _ _ same := by omega
  typed a τ d found := by
    cases a with
    | zero => cases found; exact .array _ _ _
    | succ a => cases a with
      | zero => cases found; exact .array _ _ _
      | succ a => cases a with
        | zero => cases found; exact .bytes _
        | succ a => cases a with
          | zero => cases found; exact .array _ _ _
          | succ a =>
            have absent := dynHeap.bounded (a + 4) (by change 4 ≤ a + 4; omega)
            change dynHeap.cells (a + 4) = some ⟨τ, d⟩ at found
            rw [absent] at found
            cases found
  starts a _ := by omega
  ends a present := by
    have bound : a < 4 := by
      apply Nat.lt_of_not_le
      intro no
      have absent := dynHeap.bounded a no
      rw [absent] at present
      cases present
    have size : (dynShape a).size ≤ 128 := by
      unfold dynShape
      split <;> try decide
      split <;> try decide
      split <;> decide
    change 128 + a * 256 + (dynShape a).size ≤ 1152
    omega
  separate a b _ _ different := by
    have size (i : Nat) : (dynShape i).size ≤ 128 := by
      unfold dynShape
      split <;> try decide
      split <;> try decide
      split <;> decide
    have sa := size a
    have sb := size b
    change 128 + a * 256 + (dynShape a).size ≤ 128 + b * 256 ∨ 128 + b * 256 + (dynShape b).size ≤ 128 + a * 256
    omega

def dynBase : ByteView := mstore (mstore (fun _ => 0xa5) 64 1152) 96 0
def dynPhysical := dynamicUintView 3 (by decide) dynWords
  (dynamicUintView 2 (by decide) dynOther dynBase 384) 128

theorem dyn_found : dynHeap.get 0 = some ⟨_, dynamicUintData mixedLayout 3 dynWords⟩ := rfl

theorem dyn_unchanged_heap : dynamicUintWriteback dynHeap dynPlacement 0 3 dynWords dyn_found dynPhysical = some dynHeap := by
  apply dynamicUintWriteback_unchanged
  · exact congrArg Fin.val (dynamicUint_header _ _ _ _ _)
  · exact dynamicUint_element _ _ _ _ _

def dynZeroPhysical := mstore dynPhysical 128 0
def dynZeroHeap := dynHeap.write 0 (dynamicUintData mixedLayout 0 Fin.elim0) (by rfl)

theorem dyn_zero_decode : decodeDynamicUint mixedLayout dynZeroPhysical 128 = dynamicUintData mixedLayout 0 Fin.elim0 := by
  unfold decodeDynamicUint
  rw [show mload dynZeroPhysical 128 = 0 from mload_mstore _ _ _]
  apply congrArg (dynamicUintData mixedLayout 0)
  funext i
  exact Fin.elim0 i

theorem dyn_zero_step : retainedDynamicUintWriteback dynHeap dynPlacement dynPlacement (retainInitial _ _) 0 3 dynWords dyn_found dynZeroPhysical = some dynZeroHeap := by
  simp only [retainedDynamicUintWriteback, show dynPlacement.address 0 = 128 from rfl,
    show mload dynZeroPhysical 128 = 0 from mload_mstore _ _ _]
  rw [dyn_zero_decode]
  rfl

def dynZeroPlacement := retainedDynamicUintResultPlacement dynHeap dynPlacement dynPlacement (retainInitial _ _) 0 3 dynWords dyn_found dynZeroPhysical dynZeroHeap dyn_zero_step
def dynZeroHistory := retainedDynamicUint_result_history dynHeap dynPlacement dynPlacement (retainInitial _ _) 0 3 dynWords dyn_found dynZeroPhysical dynZeroHeap dyn_zero_step

theorem dyn_zero_address : dynZeroPlacement.address = dynPlacement.address :=
  (retainedDynamicUint_choices dynHeap dynPlacement dynPlacement (retainInitial _ _) 0 3 dynWords dyn_found dynZeroPhysical dynZeroHeap dyn_zero_step).1

theorem dyn_zero_actual_shape : dynZeroPlacement.shape 0 = .array true 0 := by
  have e := (retainedDynamicUint_choices dynHeap dynPlacement dynPlacement (retainInitial _ _) 0 3 dynWords dyn_found dynZeroPhysical dynZeroHeap dyn_zero_step).2.2.1
  rw [show dynPlacement.address 0 = 128 from rfl, show mload dynZeroPhysical 128 = 0 from mload_mstore _ _ _] at e
  exact e

def dynRegrowPhysical := mstore dynZeroPhysical 128 3

theorem dyn_regrow_decode : decodeDynamicUint mixedLayout dynRegrowPhysical 128 = dynamicUintData mixedLayout 3 dynWords := by
  unfold decodeDynamicUint
  rw [show mload dynRegrowPhysical 128 = 3 from mload_mstore _ _ _]
  apply congrArg (dynamicUintData mixedLayout 3)
  funext i
  rw [mload_congr dynRegrowPhysical dynPhysical (128 + 32 + i.val * 32) (fun j => by
    change mstore (mstore dynPhysical 128 0) 128 3 (128 + 32 + i.val * 32 + j.val) = _
    rw [mstore_outside _ _ _ _ (by omega), mstore_outside _ _ _ _ (by omega)])]
  exact dynamicUint_element _ _ _ _ _ i

theorem dyn_regrow_supported : retainedDynamicUintWriteback dynZeroHeap dynPlacement dynZeroPlacement dynZeroHistory 0 0 Fin.elim0 rfl dynRegrowPhysical =
    some (dynZeroHeap.write 0 (dynamicUintData mixedLayout 3 dynWords) (by rfl)) := by
  unfold retainedDynamicUintWriteback
  rw [dyn_zero_address]
  change (if (MemoryShape.array true (mload dynRegrowPhysical 128).val).size ≤ (dynPlacement.shape 0).size then some (dynZeroHeap.write 0 (decodeDynamicUint mixedLayout dynRegrowPhysical 128) (by rfl)) else none) = _
  rw [show mload dynRegrowPhysical 128 = 3 from mload_mstore _ _ _]
  rw [dyn_regrow_decode]
  exact if_pos (by decide)

theorem dyn_minimal_api_still_rejects_regrowth : dynamicUintWriteback dynZeroHeap dynZeroPlacement 0 0 Fin.elim0 rfl dynRegrowPhysical = none := by
  unfold dynamicUintWriteback
  rw [dyn_zero_address]
  simp only [show dynPlacement.address 0 = 128 from rfl]
  rw [show mload dynRegrowPhysical 128 = 3 from mload_mstore _ _ _]
  rfl

theorem dyn_beyond_original_extent : retainedDynamicUintWriteback dynZeroHeap dynPlacement dynZeroPlacement dynZeroHistory 0 0 Fin.elim0 rfl (mstore dynZeroPhysical 128 4) = none := by
  unfold retainedDynamicUintWriteback
  rw [dyn_zero_address]
  simp only [show dynPlacement.address 0 = 128 from rfl]
  rw [mload_mstore]
  rfl

theorem dyn_tail_retained : mload dynZeroPhysical 160 = 7 ∧ mload dynZeroPhysical 192 = 9 ∧ mload dynZeroPhysical 224 = highestUint ∧
    dynZeroPhysical 256 = 0xa5 ∧ dynZeroPhysical 64 = dynPhysical 64 ∧ dynZeroPhysical 96 = dynPhysical 96 := by
  refine ⟨?_, ?_, ?_, ?_, mstore_outside _ _ _ _ (by decide), mstore_outside _ _ _ _ (by decide)⟩
  · rw [mload_congr dynZeroPhysical dynPhysical 160 (fun j => mstore_outside _ _ _ _ (by have hi := j.isLt; omega))]
    exact dynamicUint_element _ _ _ _ _ (0 : Fin 3)
  · rw [mload_congr dynZeroPhysical dynPhysical 192 (fun j => mstore_outside _ _ _ _ (by have hi := j.isLt; omega))]
    exact dynamicUint_element _ _ _ _ _ (1 : Fin 3)
  · rw [mload_congr dynZeroPhysical dynPhysical 224 (fun j => mstore_outside _ _ _ _ (by have hi := j.isLt; omega))]
    exact dynamicUint_element _ _ _ _ _ (2 : Fin 3)
  · unfold dynZeroPhysical dynPhysical
    rw [mstore_outside _ _ _ _ (by decide), dynamicUint_residual _ _ _ _ _ _ (Or.inr (by decide)), dynamicUint_residual _ _ _ _ _ _ (Or.inl (by decide))]
    decide

def dynEntry0 : MixedHeapEntry dynPlacement := ⟨0, _, dynamicUintData mixedLayout 3 dynWords, rfl,
  .words _ _ (.array (n := none) 3 (fun _ e => nomatch e) (by decide) (fun i => uintValueOfWord mixedLayout (dynWords i)) dynWords
    (fun i => .scalar _ _ (uintValueOfWord_word _ _)))⟩
def dynEntry1 : MixedHeapEntry dynPlacement := ⟨1, _, dynamicUintData mixedLayout 2 dynOther, rfl,
  .words _ _ (.array (n := none) 2 (fun _ e => nomatch e) (by decide) (fun i => uintValueOfWord mixedLayout (dynOther i)) dynOther
    (fun i => .scalar _ _ (uintValueOfWord_word _ _)))⟩
def dynEntry2 : MixedHeapEntry dynPlacement := ⟨2, _, .bytes mixedOther, rfl, .bytes _ (by decide)⟩
def dynEntry3 : MixedHeapEntry dynPlacement := ⟨3, _, .array 2 (fun _ e => (Option.some.inj e).symm) (fun _ => .val (.memRef rfl 0)), rfl,
  .words _ _ (.array 2 (fun _ e => (Option.some.inj e).symm) (by decide) (fun _ => .memRef rfl 0) (fun _ => ownedPointerWord dynPlacement 0 dynTy rfl)
    (fun _ => .pointer rfl 0 dynTy rfl rfl))⟩
def dynEntries := [dynEntry0, dynEntry1, dynEntry2, dynEntry3]

theorem dyn_coverage : CoversMixedHeap dynEntries := by
  intro a present
  have bound : a < 4 := by
    apply Nat.lt_of_not_le
    intro no
    have absent := dynHeap.bounded a no
    rw [absent] at present
    cases present
  have choices : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases choices with eq | eq | eq | eq
  · subst a; exact ⟨dynEntry0, List.mem_cons_self, rfl⟩
  · subst a; exact ⟨dynEntry1, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · subst a; exact ⟨dynEntry2, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · subst a; exact ⟨dynEntry3, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), rfl⟩

def dynState : Source.EMState mixedEnv [dynTy, dynTy] :=
  ⟨.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil),
    ⟨⟨⟨fun _ => Source.Account.empty _⟩, .empty, []⟩, dynHeap, [], [], ⟨[], .nil⟩⟩⟩
def dynZeroState := withSourceHeap dynState dynZeroHeap

theorem dyn_actual_MemOK : Source.MemOK mixedEnv dynHeap.ty dynState := by
  obtain ⟨heap, top, inner⟩ := mixedHeap_owner_invariants dynPlacement dynEntries dyn_coverage
  exact ⟨⟨⟨heap, Source.HeapTy.Le.refl _⟩, ⟨⟨dynTy, rfl, rfl⟩, ⟨⟨dynTy, rfl, rfl⟩, trivial⟩⟩⟩, top, inner⟩

theorem dyn_zero_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H dynState) : Source.MemOK mixedEnv H dynZeroState :=
  dynamicUint_write_MemOK mixedEnv H dynState 0 0 Fin.elim0 rfl ok

def dynRegrowHeap := dynZeroHeap.write 0 (dynamicUintData mixedLayout 3 dynWords) (by rfl)
def dynRegrowState := withSourceHeap dynZeroState dynRegrowHeap

theorem dyn_regrow_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H dynState) : Source.MemOK mixedEnv H dynRegrowState :=
  dynamicUint_write_MemOK mixedEnv H dynZeroState 0 3 dynWords rfl (dyn_zero_MemOK H ok)

def readDynNested : Source.EM mixedEnv [dynTy, dynTy] Nat := do
  let child ← Source.readLoc mixedReadFrame (τ := dynTy) (.mem 3 1)
  Source.lengthOf mixedReadFrame child

theorem dyn_alias_lengths_and_nested :
    (Source.lengthOf mixedReadFrame (dynZeroState.1.get .here)).run dynZeroState = (.ok 0, dynZeroState) ∧
    (Source.lengthOf mixedReadFrame (dynRegrowState.1.get .here)).run dynRegrowState = (.ok 3, dynRegrowState) ∧
    (Source.lengthOf mixedReadFrame (dynRegrowState.1.get (.there .here))).run dynRegrowState = (.ok 3, dynRegrowState) ∧
    readDynNested.run dynRegrowState = (.ok 3, dynRegrowState) := ⟨rfl, rfl, rfl, rfl⟩

theorem dyn_actual_element_read :
    (Source.readLoc (E := mixedEnv) mixedReadFrame (τ := .int Source.IntTy.u256) (.mem 0 2)).run dynRegrowState =
      (.ok (uintValueOfWord mixedLayout highestUint), dynRegrowState) := rfl

theorem dyn_other_cells : dynRegrowHeap.get 1 = dynHeap.get 1 ∧ dynRegrowHeap.get 2 = dynHeap.get 2 ∧
    dynRegrowHeap.get 3 = dynHeap.get 3 ∧ dynRegrowHeap.next = dynHeap.next := ⟨rfl, rfl, rfl, rfl⟩

def dynChanged (i : Fin 3) : Roadmap.Word := if i.val = 0 then highestUint else if i.val = 1 then 42 else 0
def dynChangedOther (i : Fin 2) : Roadmap.Word := if i.val = 0 then highestUint else 0

theorem dyn_disjoint_source_orders :
    (dynHeap.write 0 (dynamicUintData mixedLayout 3 dynChanged) (by rfl)).write 1 (dynamicUintData mixedLayout 2 dynChangedOther) (by rfl) =
    (dynHeap.write 1 (dynamicUintData mixedLayout 2 dynChangedOther) (by rfl)).write 0 (dynamicUintData mixedLayout 3 dynChanged) (by rfl) :=
  heap_writes_commute dynHeap 0 1 _ _ rfl rfl (by decide)

theorem dyn_raw_reencode : dynamicUintView (mload dynRegrowPhysical 128).val (mload dynRegrowPhysical 128).isLt
    (fun i => mload dynRegrowPhysical (128 + 32 + i.val * 32)) dynRegrowPhysical 128 = dynRegrowPhysical :=
  decodeDynamicUint_reencode _ _

theorem dyn_alias_eval_every_horizon (G : Source.Glob mixedEnv) (horizon : Nat) :
    (Source.evalE G mixedReadFrame (horizon + 2) (.length (.local (τ := dynTy) .here) rfl)).run dynRegrowState =
      (.ok (.val (uintValueOfWord mixedLayout 3)), dynRegrowState) ∧
    (Source.evalE G mixedReadFrame (horizon + 2) (.length (.local (τ := dynTy) (.there .here)) rfl)).run dynRegrowState =
      (.ok (.val (uintValueOfWord mixedLayout 3)), dynRegrowState) := ⟨rfl, rfl⟩

theorem dyn_short_horizons_preserved (G : Source.Glob mixedEnv) :
    (Source.evalE G mixedReadFrame 0 (.length (.local (τ := dynTy) .here) rfl)).run dynRegrowState = (.error .timeout, dynRegrowState) ∧
    (Source.evalE G mixedReadFrame 1 (.length (.local (τ := dynTy) .here) rfl)).run dynRegrowState = (.error .timeout, dynRegrowState) := ⟨rfl, rfl⟩

theorem dyn_disjoint_physical_orders :
    dynamicUintView 2 (by decide) dynChangedOther (dynamicUintView 3 (by decide) dynChanged dynPhysical 128) 384 =
    dynamicUintView 3 (by decide) dynChanged (dynamicUintView 2 (by decide) dynChangedOther dynPhysical 384) 128 :=
  dynamicUint_disjoint_commute _ _ _ _ _ _ _ _ _ (Or.inl (by decide))

end Solidity.Yul.Views.Controls
