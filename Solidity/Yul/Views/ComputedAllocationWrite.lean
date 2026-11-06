import Solidity.Yul.Views.ComputedAllocation
import Solidity.Yul.Views.AllocatedObjectMemory

/-! Incremental new-object encoding at computed coordinates. Only the new
object and free-pointer bytes are written; old objects and arbitrary residual
bytes are retained. This derives geometric inputs to the existing encoder,
without asserting a target allocator policy or arbitrary dirty-object support. -/
namespace Solidity.Yul.Views.ComputedAllocationWrite
open ComputedPlacement

theorem computed_fresh {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) :
    ∀ a,(h.cells a).isSome → p.address a≠p.free.val := by
  intro a present
  have choices := prepare_choices h p done
  have strict := present_strict h a h.next present (occupied_lt h a present)
  rw [choices.1,choices.2.2.1]
  omega

/-- Checked new extent is an exact Word witness, not a new runtime cap. -/
def nextFree {D : Source.Layout} {h : Source.Heap D} (p : Placement h) (shape : MemoryShape)
    (bound : p.free.val+max 1 shape.size<2^256) : Roadmap.Word :=
  ⟨p.free.val+max 1 shape.size,bound⟩

def placement {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) : Placement (h.alloc ⟨τ,data⟩).1 :=
  heapAllocPlacement h p data shape (objectShape_sound data shape found) p.free.val
    (nextFree p shape bound) (Nat.le_refl _) (computed_fresh h p done) (by dsimp [nextFree];omega)

/-- Reuse the existing actual typed object-image computation. Unsupported
canonical payloads still return None, which is not a Source/Yul verdict. -/
def prepare {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) (m : ByteView) : Option ByteView :=
  objectAllocationView h p data (objectShape_memory data shape found) shape (objectShape_sound data shape found)
    p.free.val (nextFree p shape bound) (Nat.le_refl _) (computed_fresh h p done) (by dsimp [nextFree];omega) m

theorem complete {E : Source.Env} (h : Source.Heap E.layout) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data E.layout τ)
    (shape : MemoryShape) (found : objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) (m : ByteView)
    (supported : InventoryTypeSupported E τ) (inner : Source.Data.Inner (E:=E) data)
    (valid : Source.DataOK E h.ty data) : (prepare h p done data shape found bound m).isSome :=
  objectAllocationView_complete h p data (objectShape_memory data shape found) shape
    (objectShape_sound data shape found) _ _ _ _ _ m supported inner valid

/-- Incremental encoding reconstructs the same whole raw map, and actual
unchanged writeback preserves the whole allocated Source state. Old-image
reads are genuine input agreement, not a supplied output inverse law. -/
theorem sound {E : Source.Env} {Γ : Source.RCtx} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (done : ComputedPlacement.prepare s.2.heap=.ok p)
    {τ : Source.STy} (data : Source.Data E.layout τ) (shape : MemoryShape)
    (found : objectShape data=some shape) (bound : p.free.val+max 1 shape.size<2^256)
    (m raw : ByteView) (step : prepare s.2.heap p done data shape found bound m=some raw)
    (ok : Source.MemOK E H s) (inner : Source.Data.Inner (E:=E) data)
    (valid : Source.DataOK E s.2.heap.ty data) (newSupported : InventoryTypeSupported E τ)
    (oldSupported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (reads : ∀ e∈generatedHeapEntries p,e.image.Reads m (p.address e.id)) :
    let q:=placement s.2.heap p done data shape found bound
    let after:=objectAllocatedState s data
    (Source.allocRef data).run s=(.ok (.memRef (objectShape_memory data shape found) s.2.heap.next),after) ∧
    Source.MemOK E H after ∧ CoversMixedHeap (generatedHeapEntries q) ∧
    encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
    enumeratedMemoryWriteback after q q (retainInitial _ _) raw=.ok (some (.ok (),after)) := by
  have ready := ownerMemOK_prepares_inventory H s p ok oldSupported
  have physical := objectAllocationView_computed s.2.heap p data (objectShape_memory data shape found)
    shape (objectShape_sound data shape found) p.free.val (nextFree p shape bound) (Nat.le_refl _)
    (computed_fresh s.2.heap p done) (by dsimp [nextFree];omega) _ ready m raw reads step
  have safe := (objectAllocRef_MemOK H s data (objectShape_memory data shape found)
    (objectShape_top data shape found) inner valid ok).1
  have writeback := enumeratedMemory_unchanged (objectAllocatedState s data)
    (placement s.2.heap p done data shape found bound) _ (retainInitial _ _) raw
    (heapAlloc_inventory_supported s.2.heap data newSupported oldSupported) _ physical.1
  dsimp only [placement] at writeback
  rw [physical.2.2.2] at writeback
  exact ⟨objectAllocRef_run s data (objectShape_memory data shape found),safe,physical.2.1,physical.2.2.2,writeback⟩

theorem residual {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) (m raw : ByteView)
    (step : prepare h p done data shape found bound m=some raw) (i : Nat)
    (outside : i<p.free.val ∨ p.free.val+shape.size≤i) (notFree : i<64 ∨ 96≤i) : raw i=m i := by
  obtain ⟨image,ready,span,eq,keep⟩ := objectAllocationView_region h p data (objectShape_memory data shape found)
    shape (objectShape_sound data shape found) p.free.val (nextFree p shape bound) (Nat.le_refl _)
    (computed_fresh h p done) (by dsimp [nextFree];omega) m raw step
  exact keep i (by omega) notFree

theorem reserved {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : ComputedPlacement.prepare h=.ok p) {τ : Source.STy} (data : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) (m raw : ByteView)
    (step : prepare h p done data shape found bound m=some raw) (old : ReservedOK m p.free) :
    ReservedOK raw (nextFree p shape bound) :=
  objectAllocationView_reserved h p data (objectShape_memory data shape found) shape
    (objectShape_sound data shape found) _ _ _ _ _ m raw old step
end Solidity.Yul.Views.ComputedAllocationWrite
