import Solidity.Yul.Views.NominalInventoryDynamic
import Solidity.Yul.Views.NominalRetainedControls

/-! Inventory shrink/regrowth uses actual original allocation history. Current
shape0 does not erase retained tail words or invent language refusal semantics. -/
namespace Solidity.Yul.Views.NominalInventory.DynamicControls
open Solidity.Yul.Views
open Solidity.Yul.Views.NominalMemory.RetainedControls

def words : Fin 2 → Roadmap.Word := fun i => if i.val=0 then ⟨2^256-1,by decide⟩ else 32767

def originalEntry : MixedHeapEntry placement :=
  ⟨0,arrayTy,data,rfl,.words _ _ (.array 2 (fun z (h : (none : Option Nat)=some z) => nomatch h) (by decide) values words
    (fun i => .scalar _ _ ((show ∀ j,(values j).word=some (words j) from by decide) i)))⟩

noncomputable def emptyEntry : MixedHeapEntry shrunkPlacement :=
  ⟨0,arrayTy,emptyData,rfl,.words _ _ (.array 0 (fun z (h : (none : Option Nat)=some z) => nomatch h) (by decide)
    Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i))⟩

theorem inventory_shrink : writeback state placement placement .initial [originalEntry] shrunkRaw=
    some (.ok (),shrunkState) :=
  (dynamic_compat state placement placement .initial originalEntry small rfl shrunkRaw).trans
    NominalMemory.RetainedControls.shrink_source

theorem inventory_regrow : writeback shrunkState placement shrunkPlacement shrunkHistory [emptyEntry] regrownRaw=
    some (.ok (),regrownState) :=
  (dynamic_compat shrunkState placement shrunkPlacement shrunkHistory emptyEntry small rfl regrownRaw).trans
    NominalMemory.RetainedControls.regrow_source

/-- Resetting allocation capacity to the smaller current shape loses support;
this is preparation None, not a source/Yul outcome. -/
theorem current_capacity_none :
    writeback shrunkState shrunkPlacement shrunkPlacement .initial [emptyEntry] regrownRaw=none := by
  rw [dynamic_compat shrunkState shrunkPlacement shrunkPlacement .initial emptyEntry small rfl regrownRaw]
  unfold NominalMemory.retainedState
  dsimp only [emptyEntry]
  simp only [show NominalMemory.declaredUDVT env small=true from rfl,↓reduceIte]
  rw [show mload regrownRaw (shrunkPlacement.address 0)=2 from rfl]
  exact if_neg (by decide)

theorem empty_coverage : CoversMixedHeap [emptyEntry] := by
  intro a present
  have bound : a<shrunkHeap.next := by
    apply Nat.lt_of_not_le
    intro high
    rw [shrunkHeap.bounded a high] at present
    cases present
  change a<1 at bound
  have zero : a=0 := by omega
  subst a
  exact ⟨emptyEntry,List.mem_cons_self,rfl⟩

/-- Regrowth constructs the actual current shape while retaining the original
allocation, free choice and complete supplied raw snapshot. -/
theorem regrow_view : ∃ r : InventoryRealization placement,
    regrownState=withSourceHeap shrunkState r.heap ∧ RetainedAllocation placement r.placement ∧
    r.placement.shape 0=.array true 2 ∧ r.placement.free=placement.free ∧
    encodeMixedHeap r.placement r.entries regrownRaw=regrownRaw := by
  obtain ⟨r,run,covered,distinct,types,next,addresses,free,raw⟩ :=
    writeback_view shrunkState placement shrunkPlacement shrunkHistory [emptyEntry] empty_coverage
      (by decide) regrownRaw _ inventory_regrow
  have output : regrownState=withSourceHeap shrunkState r.heap := congrArg Prod.snd run
  have heaps : regrownState.2.heap=r.heap := congrArg (fun s => s.2.heap) output
  have found : r.heap.get 0=some ⟨arrayTy,data⟩ := by rw [←heaps]; rfl
  have shape : r.placement.shape 0=.array true 2 :=
    memoryShape_unique (r.placement.typed 0 _ _ found) (.array 2 (fun z (h : (none : Option Nat)=some z) => nomatch h) _)
  exact ⟨r,output,r.history,shape,free.trans shrunkHistory.free,raw⟩

def beyond : ByteView := mstore (mstore raw 128 3) 224 0

/-- A free-pointer gap is not evidence of owned array capacity. -/
theorem beyond_fits_free : placement.address 0+(MemoryShape.array true 3).size≤placement.free.val := by decide

/-- info: (true, true) -/
#guard_msgs in #eval ((NominalMemory.decodeArray env.layout small 3 beyond (placement.address 0+32)).isSome,
  (writeback state placement placement .initial [originalEntry] beyond).isNone)

/-- Both changes preserve every original owner typing through real Source writes. -/
theorem shrink_MemOK (H : Source.HeapTy) (ok : Source.MemOK env H state) : Source.MemOK env H shrunkState :=
  writeback_MemOK H state placement placement .initial [originalEntry] shrunkRaw _ inventory_shrink ok

theorem regrow_MemOK (H : Source.HeapTy) (ok : Source.MemOK env H state) : Source.MemOK env H regrownState :=
  writeback_MemOK H shrunkState placement shrunkPlacement shrunkHistory [emptyEntry] regrownRaw _ inventory_regrow
    (shrink_MemOK H ok)

theorem actual_regrow_MemOK : Source.MemOK env heap.ty regrownState :=
  regrow_MemOK heap.ty NominalMemory.RetainedControls.actual_MemOK

/-- info: true -/
#guard_msgs in #eval decide (mload shrunkRaw 160=⟨2^256-1,by decide⟩ ∧
  mload regrownRaw 192=32767 ∧ shrunkRaw 240=165 ∧ regrownRaw 240=165 ∧
  mload regrownRaw 64=256 ∧ mload regrownRaw 96=0)

end Solidity.Yul.Views.NominalInventory.DynamicControls
