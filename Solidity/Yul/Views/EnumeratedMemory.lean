import Solidity.Yul.Views.HeapEnumerationLaws
import Solidity.Yul.Views.HeapPreparationMemOK
import Solidity.Yul.Views.InventoryView

namespace Solidity.Yul.Views

/-- Outer errors report the exact unsupported occupied IDs, BEFORE source
execution. Inner None retains the original snapshot decoder's preparation
meaning. Neither is a source/Yul halt, no-op, cleaning, or deallocation. -/
def enumeratedMemoryWriteback {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (m : ByteView) :
    Except (List Nat) (Option (Except Source.Halt Unit × Source.EMState E Γ)) :=
  (prepareHeapInventory p).map (fun es => inventoryStateWriteback s allocated p history es m)

def enumeratedMemoryView {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (residual : ByteView) :
    Except (List Nat) ByteView := (prepareHeapInventory p).map (fun es => encodeMixedHeap p es residual)

theorem enumeratedMemoryWriteback_MemOK {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : enumeratedMemoryWriteback s allocated p history m = .ok (some result)) (ok : Source.MemOK E H s) :
    Source.MemOK E H result.2 := by
  unfold enumeratedMemoryWriteback at step
  cases prepared : prepareHeapInventory p with
  | error bad => rw [prepared] at step; cases step
  | ok es =>
    rw [prepared] at step
    exact inventoryStateWriteback_MemOK H s allocated p history es m result (Except.ok.inj step) ok

/-- No supplied entries, coverage, inverse, safety, or final-view witnesses.
Coverage, uniqueness, current placements, raw view and source success are all
constructed from the computed finite inventory and existing concrete decoder. -/
theorem enumeratedMemoryWriteback_view {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : enumeratedMemoryWriteback s allocated p history m = .ok (some result)) :
    ∃ realized : InventoryRealization allocated,
      result = (.ok (),withSourceHeap s realized.heap) ∧ CoversMixedHeap realized.entries ∧
      (realized.entries.map MixedHeapEntry.id).Nodup ∧ encodeMixedHeap realized.placement realized.entries m = m := by
  unfold enumeratedMemoryWriteback at step
  cases prepared : prepareHeapInventory p with
  | error bad => rw [prepared] at step; cases step
  | ok es =>
    rw [prepared] at step
    have facts := prepareHeapInventory_ok p es prepared
    exact inventoryStateWriteback_view s allocated p history es facts.2.1 facts.2.2 m result (Except.ok.inj step)

theorem enumeratedMemoryWriteback_realization {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : enumeratedMemoryWriteback s allocated p history m = .ok (some result)) :
    ∃ realized : InventoryRealization allocated,
      result = (.ok (),withSourceHeap s realized.heap) ∧ CoversMixedHeap realized.entries ∧
      realized.heap.ty = s.2.heap.ty ∧ realized.heap.next = s.2.heap.next ∧
      realized.placement.address = p.address ∧ realized.placement.free = p.free ∧
      ∀ τ w, decodeExtendedMemoryMember realized.placement realized.entries τ w = decodeExtendedMemoryMember p (generatedHeapEntries p) τ w := by
  unfold enumeratedMemoryWriteback at step
  cases prepared : prepareHeapInventory p with
  | error bad => rw [prepared] at step; cases step
  | ok es =>
    rw [prepared] at step
    have facts := prepareHeapInventory_ok p es prepared
    have same := facts.1
    rw [← same]
    exact inventoryStateWriteback_realization s allocated p history es facts.2.1 m result (Except.ok.inj step)

theorem enumeratedMemoryView_reserved {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (residual m : ByteView)
    (reserved : ReservedOK residual p.free) (view : enumeratedMemoryView p residual = .ok m) : ReservedOK m p.free := by
  unfold enumeratedMemoryView at view
  cases prepared : prepareHeapInventory p with
  | error bad => rw [prepared] at view; cases view
  | ok es =>
    rw [prepared] at view
    cases view
    exact encodeMixedHeap_reserved p es residual reserved

/-- Exact whole source-state identity for canonical supported constructors,
using computed entries and their OWN encoded view. This is not a full-memory
support claim: declared-type support is explicit and dirty words stay open. -/
theorem enumeratedMemory_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (residual : ByteView)
    (supported : ∀ a τ d, s.2.heap.get a = some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (es : List (MixedHeapEntry p)) (prepared : prepareHeapInventory p = .ok es) :
    enumeratedMemoryWriteback s allocated p history (encodeMixedHeap p es residual) = .ok (some (.ok (),s)) := by
  have facts := prepareHeapInventory_ok p es prepared
  unfold enumeratedMemoryWriteback
  rw [prepared]
  change Except.ok (inventoryStateWriteback s allocated p history es (encodeMixedHeap p es residual)) = _
  rw [inventoryStateWriteback_unchanged s allocated p history es facts.2.1
    (fun e _ => supported e.id e.ty e.data e.found) _ (encodeMixedHeap_reads p es facts.2.2 residual)]

/-- A direct owner-state entrypoint: no manually supplied inventory OR
representability/coverage witness. Existing MemOK and supported declared types
construct preparation, exact readback and whole-state unchanged identity. -/
theorem ownerMemory_unchanged {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (residual : ByteView) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d, s.2.heap.get a = some ⟨τ,d⟩ → InventoryTypeSupported E τ) :
    enumeratedMemoryView p residual = .ok (encodeMixedHeap p (generatedHeapEntries p) residual) ∧
    enumeratedMemoryWriteback s allocated p history (encodeMixedHeap p (generatedHeapEntries p) residual) = .ok (some (.ok (),s)) := by
  have prepared := ownerMemOK_prepares_inventory H s p ok supported
  exact ⟨by unfold enumeratedMemoryView; rw [prepared]; rfl,
    enumeratedMemory_unchanged s allocated p history residual supported _ prepared⟩

theorem enumeratedMemoryWriteback_reads {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : enumeratedMemoryWriteback s allocated p history m = .ok (some result)) :
    ∃ realized : InventoryRealization allocated,
      result = (.ok (),withSourceHeap s realized.heap) ∧
      (∀ a τ (data : Source.Data E.layout τ) off w, realized.heap.get a = some ⟨τ,data⟩ →
        ObjectWord realized.placement.address data off w → mload m (realized.placement.address a+off) = w) ∧
      (∀ a τ (data : Source.Data E.layout τ) off b, realized.heap.get a = some ⟨τ,data⟩ →
        ObjectByte data off b → m (realized.placement.address a+off) = b) := by
  unfold enumeratedMemoryWriteback at step
  cases prepared : prepareHeapInventory p with
  | error bad => rw [prepared] at step; cases step
  | ok es =>
    rw [prepared] at step
    have facts := prepareHeapInventory_ok p es prepared
    exact inventoryStateWriteback_reads s allocated p history es facts.2.1 facts.2.2 m result (Except.ok.inj step)

theorem enumeratedMemoryWriteback_reserved {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (m : ByteView) (reserved : ReservedOK m p.free)
    (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : enumeratedMemoryWriteback s allocated p history m = .ok (some result)) :
    ∃ realized : InventoryRealization allocated, result = (.ok (),withSourceHeap s realized.heap) ∧
      ReservedOK (encodeMixedHeap realized.placement realized.entries m) realized.placement.free := by
  unfold enumeratedMemoryWriteback at step
  cases prepared : prepareHeapInventory p with
  | error bad => rw [prepared] at step; cases step
  | ok es =>
    rw [prepared] at step
    have facts := prepareHeapInventory_ok p es prepared
    exact inventoryStateWriteback_reserved s allocated p history es facts.2.1 facts.2.2 m reserved result (Except.ok.inj step)

theorem enumeratedMemoryWriteback_sequential {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (m : ByteView) :
    enumeratedMemoryWriteback s allocated p history m = (prepareHeapInventory p).map (fun es =>
      (sequentialInventory allocated p history es s.2.heap p history rfl es m).map
        (fun realized => ((.ok () : Except Source.Halt Unit),withSourceHeap s realized.heap))) := by
  unfold enumeratedMemoryWriteback
  cases prepareHeapInventory p with
  | error bad => rfl
  | ok es => exact congrArg Except.ok (inventoryStateWriteback_sequential s allocated p history es m)

end Solidity.Yul.Views
