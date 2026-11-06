import Solidity.Yul.Views.ResidualMemoryWriteback

namespace Solidity.Yul.Views

/-- A physical copy request, indexed by the existing actual placement. The
source bound is an arithmetic EVM interval condition, not an adequacy premise.
These are preparation inputs, not a second Yul syntax or Source state. -/
structure ResidualCopyRequest {D : Source.Layout} {h : Source.Heap D} (p : Placement h) where
  window : ResidualWindowPlan p
  source : Roadmap.Word
  sourceRange : ValidRange source.val window.size.val

/-- Complete current typed physical snapshot, including residual bytes. -/
def residualCopyPhysical {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (residual : ByteView) : ByteView := encodeMixedHeap p (generatedHeapEntries p) residual

/-- Read the current physical snapshot ONCE. In particular the source is not
just residual memory, and overlapping copies never read their own new bytes. -/
def ResidualCopyRequest.apply {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (request : ResidualCopyRequest p) (residual : ByteView) : ByteView :=
  copyBytes residual (residualCopyPhysical p residual) request.window.destination.val
    request.source.val request.window.size.val

theorem ResidualCopyRequest.physical {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (request : ResidualCopyRequest p) (residual : ByteView) :
    residualCopyPhysical p (request.apply residual)=
      mcopy (residualCopyPhysical p residual) request.window.destination.val request.source.val request.window.size.val := by
  have same := request.window.inventory.1
  have frame := request.window.whole_map residual (residualCopyPhysical p residual) request.source.val
  rw [same] at frame
  exact frame.symm

theorem ResidualCopyRequest.reserved {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (request : ResidualCopyRequest p) (residual : ByteView) (ok : ReservedOK residual p.free) :
    ReservedOK (request.apply residual) p.free := request.window.reserved _ _ _ ok

/-- Chronological copies over the actual finite request list; there is no
additional fuel, depth, length, or resource cap. Each next source sees the
previous complete physical snapshot. -/
def residualCopies {D : Source.Layout} {h : Source.Heap D} {p : Placement h} :
    List (ResidualCopyRequest p) → ByteView → ByteView
  | [],residual => residual
  | request::rest,residual => residualCopies rest (request.apply residual)

/-- The ordinary physical mcopy operations, with exactly the same order. -/
def physicalCopies {D : Source.Layout} {h : Source.Heap D} {p : Placement h} :
    List (ResidualCopyRequest p) → ByteView → ByteView
  | [],physical => physical
  | request::rest,physical => physicalCopies rest
      (mcopy physical request.window.destination.val request.source.val request.window.size.val)

theorem residualCopies_physical {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (requests : List (ResidualCopyRequest p)) (residual : ByteView) :
    residualCopyPhysical p (residualCopies requests residual)=physicalCopies requests (residualCopyPhysical p residual) := by
  induction requests generalizing residual with
  | nil => rfl
  | cons request rest ih =>
    change residualCopyPhysical p (residualCopies rest (request.apply residual))=_
    rw [ih,request.physical]
    rfl

theorem residualCopies_append {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (before after : List (ResidualCopyRequest p)) (residual : ByteView) :
    residualCopies (before++after) residual=residualCopies after (residualCopies before residual) := by
  induction before generalizing residual with
  | nil => rfl
  | cons request rest ih => exact ih (request.apply residual)

theorem residualCopies_reserved {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (requests : List (ResidualCopyRequest p)) (residual : ByteView) (ok : ReservedOK residual p.free) :
    ReservedOK (residualCopies requests residual) p.free := by
  induction requests generalizing residual with
  | nil => exact ok
  | cons request rest ih => exact ih _ (request.reserved residual ok)

/-- Unknown bytes outside every destination retain their original exact value. -/
theorem residualCopies_outside {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (requests : List (ResidualCopyRequest p)) (residual : ByteView) (a : Nat)
    (outside : ∀ request ∈ requests, ¬(request.window.destination.val≤a ∧
      a<request.window.destination.val+request.window.size.val)) :
    residualCopies requests residual a=residual a := by
  induction requests generalizing residual with
  | nil => rfl
  | cons request rest ih =>
    change residualCopies rest (request.apply residual) a=residual a
    rw [ih _ (fun other member=>outside other (List.mem_cons_of_mem _ member))]
    exact copyBytes_outside _ _ _ _ _ _ (outside request (List.mem_cons_self))

/-- EVERY chronological request invokes the existing concrete source
writeback on the current physical snapshot. The equality is derived, not a
caller-supplied coverage, inverse, safety, or final-view hypothesis. -/
theorem residualCopy_actual_step {E Γ origin}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (request : ResidualCopyRequest p) (residual : ByteView)
    (supported : ∀ a ty d, s.2.heap.get a=some ⟨ty,d⟩ → InventoryTypeSupported E ty) :
    residualMemoryWriteback s allocated p history request.window residual
      (residualCopyPhysical p residual) request.source.val=
      .ok (some ((.ok (),s),request.apply residual)) :=
  residualMemoryWriteback_exact s allocated p history request.window residual _ _ supported

/-- A single concrete final source writeback after the chronological physical
copies. Preparation failures retain their existing Except/Option meaning. -/
def residualCopiesWriteback {E Γ origin}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (requests : List (ResidualCopyRequest p)) (residual : ByteView) :=
  let after:=residualCopies requests residual
  (enumeratedMemoryWriteback s allocated p history (physicalCopies requests (residualCopyPhysical p residual))).map
    fun result=>result.map fun source=>(source,match source.1 with | .ok _=>after | .error _=>residual)

theorem residualCopiesWriteback_exact {E Γ origin}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (requests : List (ResidualCopyRequest p)) (residual : ByteView)
    (supported : ∀ a ty d, s.2.heap.get a=some ⟨ty,d⟩ → InventoryTypeSupported E ty)
    (prepared : prepareHeapInventory p=.ok (generatedHeapEntries p)) :
    residualCopiesWriteback s allocated p history requests residual=
      .ok (some ((.ok (),s),residualCopies requests residual)) := by
  unfold residualCopiesWriteback
  rw [←residualCopies_physical]
  unfold residualCopyPhysical
  rw [enumeratedMemory_unchanged s allocated p history _ supported (generatedHeapEntries p) prepared]
  rfl

/-- Actual whole-state identity preserves EVERY original owner typing. -/
theorem residualCopiesWriteback_every_H {E Γ origin}
    (H : Source.HeapTy) (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (requests : List (ResidualCopyRequest p)) (residual : ByteView)
    (supported : ∀ a ty d, s.2.heap.get a=some ⟨ty,d⟩ → InventoryTypeSupported E ty)
    (ok : Source.MemOK E H s) :
    ∃ after, residualCopiesWriteback s allocated p history requests residual=.ok (some after) ∧
      Source.MemOK E H after.1.2 :=
  ⟨((.ok (),s),residualCopies requests residual),
    residualCopiesWriteback_exact s allocated p history requests residual supported
      (ownerMemOK_prepares_inventory H s p ok supported),ok⟩

/-- Every actual step after an arbitrary prefix uses that prefix's refreshed
physical snapshot, and returns the SAME complete source state. -/
theorem residualCopies_prefix_step {E Γ origin}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (before : List (ResidualCopyRequest p))
    (request : ResidualCopyRequest p) (residual : ByteView)
    (supported : ∀ a ty d, s.2.heap.get a=some ⟨ty,d⟩ → InventoryTypeSupported E ty) :
    residualMemoryWriteback s allocated p history request.window (residualCopies before residual)
      (residualCopyPhysical p (residualCopies before residual)) request.source.val=
      .ok (some ((.ok (),s),residualCopies (before++[request]) residual)) := by
  rw [residualCopies_append]
  exact residualCopy_actual_step s allocated p history request _ supported

/-- Full canonical decoded contents and aliases are untouched at every copy
step; raw residual bytes can still change. Resource/callee adequacy is OPEN. -/
theorem ResidualCopyRequest.readback {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    (request : ResidualCopyRequest p) (residual : ByteView) :
    readBytes (residualCopyPhysical p (request.apply residual)) request.window.destination.val request.window.size.val=
      readBytes (residualCopyPhysical p residual) request.source.val request.window.size.val := by
  rw [request.physical]
  unfold readBytes
  apply List.map_congr_left
  intro i member
  exact find_copyBytes _ _ _ _ _ i (List.mem_range.mp member)

end Solidity.Yul.Views
