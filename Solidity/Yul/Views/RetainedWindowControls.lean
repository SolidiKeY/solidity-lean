import Solidity.Yul.Views.RetainedResidualGeometry
import Solidity.Yul.Views.RetainedByteControls

namespace Solidity.Yul.Views.RetainedWindowControls
open Controls

theorem padding_geometry : ResidualWindowDisjoint retainedEmptyPlacement
    (generatedHeapEntries retainedEmptyPlacement) 160 3 :=
  retained_byte_padding_disjoint (bytePlacement 0) retainedEmptyPlacement retainedEmpty
    (generatedHeapEntries retainedEmptyPlacement) 0 [] rfl 160 3 (by decide) (by decide)

theorem empty_supported (a : Nat) (ty : Source.STy) (data : Source.Data heapByteEnv.layout ty)
    (found : emptyHeap.get a=some ⟨ty,data⟩) : InventoryTypeSupported heapByteEnv ty := by
  cases a with
  | zero =>
    change some (⟨.bytes .memory,Source.Data.bytes []⟩ : Σ ty,Source.Data heapByteEnv.layout ty)=some ⟨ty,data⟩ at found
    cases found
    trivial
  | succ a =>
    unfold emptyHeap at found
    rw [Source.Heap.write_other byteHeap (by omega)] at found
    cases a with
    | zero =>
      change some (⟨.string .memory,Source.Data.string stringOld⟩ : Σ ty,Source.Data heapByteEnv.layout ty)=some ⟨ty,data⟩ at found
      cases found
      trivial
    | succ a =>
      cases a with
      | zero =>
        change some (⟨.bytes .memory,Source.Data.bytes byteOther⟩ : Σ ty,Source.Data heapByteEnv.layout ty)=some ⟨ty,data⟩ at found
        cases found
        trivial
      | succ a =>
        have missing := byteHeap.bounded (a+3) (by change 3≤a+3; omega)
        change byteHeap.cells (a+3)=some ⟨ty,data⟩ at found
        rw [missing] at found
        cases found

theorem empty_prepared : prepareHeapInventory retainedEmptyPlacement=.ok (generatedHeapEntries retainedEmptyPlacement) :=
  ownerMemOK_prepares_inventory byteHeap.ty emptyState retainedEmptyPlacement actual_resize_MemOK.2.2 empty_supported

theorem padding_checked : residualWindowCheck retainedEmptyPlacement (generatedHeapEntries retainedEmptyPlacement) 160 3=true :=
  (residualWindowCheck_iff _ _ _ _).mpr ⟨by decide,Or.inr (Or.inr (by decide)),padding_geometry⟩

def paddingPlan : ResidualWindowPlan retainedEmptyPlacement :=
  ⟨160,3,generatedHeapEntries retainedEmptyPlacement,empty_prepared,padding_checked⟩

theorem padding_plan_computed : prepareResidualWindow retainedEmptyPlacement 160 3=.ok (some paddingPlan) :=
  prepareResidualWindow_plan paddingPlan

def paddingSource : ByteView := calldataBytes [0xde,0xad,0x77]
def paddingRaw := copyBytes (encodeMixedHeap retainedEmptyPlacement paddingPlan.entries emptyPhysical) paddingSource 160 0 3

theorem no_lost_original_ownership : (retainedEmptyPlacement.shape 0).size=32 ∧
    ((bytePlacement 0).shape 0).size=64 ∧ retainedEmptyPlacement.address 0=128 := ⟨rfl,rfl,rfl⟩

theorem padding_whole_state : residualMemoryWriteback emptyState (bytePlacement 0) retainedEmptyPlacement retainedEmpty
    paddingPlan emptyPhysical paddingSource 0=
      .ok (some ((.ok (),emptyState),copyBytes emptyPhysical paddingSource 160 0 3)) :=
  residualMemoryWriteback_exact emptyState (bytePlacement 0) retainedEmptyPlacement retainedEmpty paddingPlan
    emptyPhysical paddingSource 0 empty_supported

def regrowRaw := mstore paddingRaw 128 3
def regrowHeap := emptyHeap.write 0 (Source.Data.bytes [0xde,0xad,0x77]) (by rfl)

theorem padding_then_actual_regrowth : retainedByteWriteback emptyHeap (bytePlacement 0) retainedEmptyPlacement retainedEmpty
    0 false [] rfl regrowRaw=some regrowHeap := by
  simp only [retainedByteWriteback,regrowRaw,show retainedEmptyPlacement.address 0=128 from rfl,mload_mstore]
  rw [if_pos (by decide),decodeHeapByte_data,mload_mstore]
  simp only [show (3 : Roadmap.Word).val=3 from rfl,show (128+32 : Nat)=160 from rfl]
  have payload : readBytes (mstore paddingRaw 128 3) 160 3=[0xde,0xad,0x77] := by decide
  rw [payload]
  rfl

def regrowState := withSourceHeap emptyState regrowHeap

theorem actual_regrowth_state : retainedByteStateWriteback emptyState (bytePlacement 0) retainedEmptyPlacement retainedEmpty
    0 false [] rfl regrowRaw=some regrowState := by
  change (retainedByteWriteback emptyHeap _ _ _ _ _ _ rfl _).map (withSourceHeap emptyState)=_
  rw [padding_then_actual_regrowth]
  rfl

theorem every_original_H (H : Source.HeapTy) (ok : Source.MemOK heapByteEnv H emptyState) :
    Source.MemOK heapByteEnv H regrowState :=
  retainedByteState_MemOK heapByteEnv H _ _ _ _ retainedEmpty 0 false [] rfl _ actual_regrowth_state ok

theorem both_actual_alias_reads (horizon : Nat) :
    (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame horizon (.val (regrowState.1.get .here))).run regrowState=
      (.ok [0xde,0xad,0x77],regrowState) ∧
    (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame horizon (.val (regrowState.1.get (.there .here)))).run regrowState=
      (.ok [0xde,0xad,0x77],regrowState) := ⟨rfl,rfl⟩

end Solidity.Yul.Views.RetainedWindowControls
