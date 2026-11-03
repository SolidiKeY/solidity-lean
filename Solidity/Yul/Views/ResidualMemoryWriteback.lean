import Solidity.Yul.Views.ResidualHeapGeometry

namespace Solidity.Yul.Views

theorem ResidualWindowPlan.facts {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (plan : ResidualWindowPlan p) :
    plan.destination.val+plan.size.val≤2^256 ∧
    (plan.size.val=0 ∨ plan.destination.val+plan.size.val≤64 ∨ 128≤plan.destination.val) ∧
    ResidualWindowDisjoint p plan.entries plan.destination.val plan.size.val :=
  (residualWindowCheck_iff _ _ _ _).mp plan.checked

theorem ResidualWindowPlan.inventory {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (plan : ResidualWindowPlan p) : plan.entries=generatedHeapEntries p ∧
      CoversMixedHeap plan.entries ∧ (plan.entries.map MixedHeapEntry.id).Nodup :=
  prepareHeapInventory_ok p plan.entries plan.prepared

theorem ResidualWindowPlan.whole_map {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (plan : ResidualWindowPlan p) (residual src : ByteView) (start : Nat) :
    copyBytes (encodeMixedHeap p plan.entries residual) src plan.destination.val start plan.size.val=
      encodeMixedHeap p plan.entries (copyBytes residual src plan.destination.val start plan.size.val) :=
  encodeMixedHeap_disjoint_copy p plan.entries residual src _ _ _ plan.facts.2.2

theorem ResidualWindowPlan.reserved {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (plan : ResidualWindowPlan p) (residual src : ByteView) (start : Nat) (reserved : ReservedOK residual p.free) :
    ReservedOK (copyBytes residual src plan.destination.val start plan.size.val) p.free :=
  disjoint_copy_reserved residual src p.free _ _ _ plan.facts.2.1 reserved

/-- Constructive physical range check -> computed exact Source writeback.
The input profile is the EXISTING typed codec domain, not language admission.
The prepared entries are computed, not caller-supplied finished coverage laws. -/
theorem ResidualWindowPlan.source_unchanged {E Γ origin}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (plan : ResidualWindowPlan p)
    (residual src : ByteView) (start : Nat)
    (supported : ∀ a ty d, s.2.heap.get a=some ⟨ty,d⟩ → InventoryTypeSupported E ty) :
    enumeratedMemoryView p (copyBytes residual src plan.destination.val start plan.size.val)=
      .ok (copyBytes (encodeMixedHeap p plan.entries residual) src plan.destination.val start plan.size.val) ∧
    enumeratedMemoryWriteback s allocated p history
      (copyBytes (encodeMixedHeap p plan.entries residual) src plan.destination.val start plan.size.val)=
        .ok (some (.ok (),s)) := by
  rw [plan.whole_map]
  refine ⟨?_,enumeratedMemory_unchanged s allocated p history _ supported plan.entries plan.prepared⟩
  unfold enumeratedMemoryView
  rw [plan.prepared]
  rfl

/-- This is preparation over an actual Source operation result. Residual bytes
advance ONLY on actual source success; source errors keep their exact prefix
and old residual. Outer/inner preparation failures are not language verdicts. -/
def residualMemoryWriteback {E Γ origin}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (plan : ResidualWindowPlan p)
    (residual src : ByteView) (start : Nat) :
    Except (List Nat) (Option ((Except Source.Halt Unit × Source.EMState E Γ) × ByteView)) :=
  let raw:=copyBytes (encodeMixedHeap p plan.entries residual) src plan.destination.val start plan.size.val
  (enumeratedMemoryWriteback s allocated p history raw).map fun result=>
    result.map fun source =>
      (source,match source.1 with
        | .ok _ => copyBytes residual src plan.destination.val start plan.size.val
        | .error _ => residual)

theorem residualMemoryWriteback_exact {E Γ origin}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (plan : ResidualWindowPlan p)
    (residual src : ByteView) (start : Nat)
    (supported : ∀ a ty d, s.2.heap.get a=some ⟨ty,d⟩ → InventoryTypeSupported E ty) :
    residualMemoryWriteback s allocated p history plan residual src start=
      .ok (some ((.ok (),s),copyBytes residual src plan.destination.val start plan.size.val)) := by
  unfold residualMemoryWriteback
  dsimp only
  rw [(plan.source_unchanged s allocated p history residual src start supported).2]
  rfl

/-- Every ORIGINAL owner heap typing is preserved, because the complete source
state in the actual supported result is equal, not a replacement MemOK. -/
theorem residualMemoryWriteback_every_H {E Γ origin}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (plan : ResidualWindowPlan p)
    (residual src : ByteView) (start : Nat)
    (supported : ∀ a ty d, s.2.heap.get a=some ⟨ty,d⟩ → InventoryTypeSupported E ty)
    (ok : Source.MemOK E H s) :
    ∃ after, residualMemoryWriteback s allocated p history plan residual src start=.ok (some after) ∧
      Source.MemOK E H after.1.2 :=
  ⟨((.ok (),s),copyBytes residual src plan.destination.val start plan.size.val),
    residualMemoryWriteback_exact s allocated p history plan residual src start supported,ok⟩

end Solidity.Yul.Views
