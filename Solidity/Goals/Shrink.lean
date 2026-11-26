import Solidity.Yul.Layout.Shared.Contracts
import Solidity.Tools.Goal
import Solidity.Yul.Views.FinitePaths
import Solidity.Yul.Views.FiniteCellWrites
import Solidity.Yul.Views.MemberArray
import Solidity.Yul.Views.ByteObjects
import Solidity.Yul.Views.HeapByteAllocation
import Solidity.Yul.Views.ObjectMemoryAllocation
import Solidity.Yul.Views.EnumeratedMemory
import Solidity.Yul.Views.JointMemory

/-!
# The two shrink goals (H517)

Two open targets, stated here and proved by later lanes (yv1–yv3, ls1–ls4).
Neither replaces the historical `genericYulViewsPreserve` of `Goals/Plan.lean`.
The lowering goal `loweringBySimulation` is stated in `Goals/LoweringSim.lean`.

* `yulLayoutView` (`Solidity.Yul.Layout.view_correct`): ONE view defined by
  structural recursion over an inductive layout description (`Shrink.Layout`),
  with read-after-write, frame, failure and allocation laws proved once, and
  an instance relation that pins the view to every existing per-shape view
  definition of `Solidity/Yul/Views` (inventory below).
  Its Scalar pilot `yulLayoutPilot` (`Solidity.Yul.Layout.pilot_correct`)
  asks for the same laws and only the scalar correspondence (`ScalarPilot`).

## Views inventory (per-shape view definitions, read at the launch base)

| Shape | Declaration | Pinned by |
|---|---|---|
| packed storage/transient scalar | `scalarPathView`, `patchScalarSlot` (ScalarWriteback.lean:95,100) | `Geometric.scalar`, `Instances.scalarPath` |
| finite separated scalar paths | `finiteView`, `pathsApart` (FinitePaths.lean:17,30) | `Instances.scalarPath`, `Instances.apart` |
| persistent + transient cells | `FiniteCellWrites.Views` (FiniteCellWrites.lean:26) | `Instances.cells` |
| mappings, dynamic data | `physicalSlot` over `Storage.Loc.hash`/`.data` (Packing.lean:39) | `Geometric.key`, `Geometric.data`, `Geometric.length` |
| packed arrays and scalar structs | `packedStart` (PackedAggregates.lean:54) | `Geometric.elem`, `Geometric.field` |
| fixed word array in memory | `wordListView` (AggregateMemoryWords.lean:8) | `Instances.wordList` |
| dynamic word / member array | `dynamicUintView`, `memberArrayView` (DynamicUintMemory.lean:12, MemberArray.lean:121) | `Instances.memberArray` |
| bytes/string object | `bytesObjectView` (ByteObjects.lean:13) | `Instances.bytesObject` |
| bytes allocation | `byteAllocationView` (HeapByteAllocation.lean:51) | `Instances.byteAllocation` |
| any heap object allocation | `objectAllocationView` (ObjectMemoryAllocation.lean:37) | `Instances.objectAllocation` |
| whole placed heap | `enumeratedMemoryView`, `Placement` (EnumeratedMemory.lean:16, MemoryContract.lean:48) | `Instances.enumerated` |
| narrow memory values | dirty-bit cleaning | `Geometric.memoryScalar` (`Params.cleanDirty`) |

Families built from these primitives without a conjunct of their own (their
encoders are folds of the pinned scalar, key, data and packing placements):
`WordMappingRoot.encode` (MappingSlots.lean:92), `NestedWordMappingRoot.encode`
(NestedMappingSlots.lean:110), `PackedMembers.encode` (PackedAggregates.lean:95),
`encodeStructArray` (StructArray.lean:186), `encodeArrayStruct`
(ArrayStruct.lean:86), `RecursiveStorageDeclaration.pack`
(RecursiveStorageDeclaration.lean:24), `reencodePersistentSlot`
(PackedResidualWorld.lean:40), `MemoryElement`/`MemoryFields`
(AggregateMemoryWords.lean:69,96), `encodeMixedHeap` (MixedHeapView.lean:14),
`CellHashMemory.image` (CellHashMemory.lean:15) and the obligation records
`ScalarStorageObligations` (StorageContract.lean:30),
`MemoryLayoutObligations` (MemoryLayout.lean:53). Equation conjuncts for
each are open work for yv2/yv3, not claimed here.
-/

namespace Solidity.Goals.Shrink

open Solidity.Yul.Views

/-! ## Layout-indexed view -/


/-- **The instance relation**: each existing per-shape view definition is the
recursive view at a concrete layout, location and tree. -/
structure LayoutView.Instances (V : LayoutView) : Prop where
  /-- `scalarPathView`, at every path, codec, store and slot region. -/
  scalarPath : ∀ (P : Params) {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (m : Phys),
    scalarPathView p c slot s m.storage ↔
      (s.read p).map (fun v => Tree.leaf (c.encode v).val) =
        V.geometry.read P (.scalar f.width) ⟨.storage, slot.val, f.offset⟩ m
  /-- `pathsApart`: separation is footprint disjointness. -/
  apart : ∀ (P : Params) {D : Source.Layout} {L : Source.SPath → Source.STy}
    (c d : ScalarPath D L) (m : Phys),
    pathsApart c d ↔ Apart (V.geometry.cells P (.scalar c.field.width)
        ⟨.storage, c.slot.val, c.field.offset⟩ m)
      (V.geometry.cells P (.scalar d.field.width) ⟨.storage, d.slot.val, d.field.offset⟩ m)
  /-- `FiniteCellWrites.Views`: persistent and transient paths of one frame. -/
  cells : ∀ (P : Params) {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr)
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (source : Source.EMState E Γ) (m : Phys),
    FiniteCellWrites.Views F ps ts source (m.storage, m.transient) ↔
      (∀ c ∈ ps, ((source.2.ex.world.accounts F.this).storage.read c.path).map
          (fun v => Tree.leaf (c.codec.encode v).val) =
        V.geometry.read P (.scalar c.field.width) ⟨.storage, c.slot.val, c.field.offset⟩ m) ∧
      (∀ c ∈ ts, ((source.2.ex.transient.cells F.this).read c.path).map
          (fun v => Tree.leaf (c.codec.encode v).val) =
        V.geometry.read P (.scalar c.field.width) ⟨.transient, c.slot.val, c.field.offset⟩ m)
  /-- `wordListView`: a fixed array of words, and exactly its bytes. -/
  wordList : ∀ (P : Params) (ws : List Roadmap.Word) (r : ByteView) (base : Nat) (m : Phys),
    V.geometry.read P (.fixedArray (.scalar 32) ws.length) ⟨.memory, base, 0⟩
        (m.withMemory (wordListView ws r base)) = some (.node (ws.map fun w => .leaf w.val)) ∧
    ∀ x, V.geometry.cells P (.fixedArray (.scalar 32) ws.length) ⟨.memory, base, 0⟩
        (m.withMemory (wordListView ws r base)) x ↔ objectCells base (ws.length * 32) x
  /-- `memberArrayView` (and so `dynamicUintView`): a dynamic array when
  unsized (length word, then words), fixed otherwise, and exactly its bytes. -/
  memberArray : ∀ (P : Params) (k : Option Nat) (n : Nat) (bound : n < 2 ^ 256)
    (words : Fin n → Roadmap.Word) (r : ByteView) (base : Nat) (m : Phys),
    V.geometry.read P (memoryShapeLayout (.array k.isNone n)) ⟨.memory, base, 0⟩
        (m.withMemory (memberArrayView k n bound words r base)) =
      some (.node ((List.ofFn words).map fun w => .leaf w.val)) ∧
    ∀ x, V.geometry.cells P (memoryShapeLayout (.array k.isNone n)) ⟨.memory, base, 0⟩
        (m.withMemory (memberArrayView k n bound words r base)) x ↔
      objectCells base (MemoryShape.array k.isNone n).size x
  /-- `bytesObjectView`: a bytes/string object (length word, then bytes); its
  footprint lies in the object (padding is not read). -/
  bytesObject : ∀ (P : Params) (bs : List UInt8) (bound : bs.length < 2 ^ 256)
    (r : ByteView) (base : Nat) (m : Phys),
    V.geometry.read P .bytes ⟨.memory, base, 0⟩ (m.withMemory (bytesObjectView bs bound r base)) =
      some (.blob bs) ∧
    ∀ x, V.geometry.cells P .bytes ⟨.memory, base, 0⟩
        (m.withMemory (bytesObjectView bs bound r base)) x →
      objectCells base ((MemoryShape.bytes bs.length).size) x
  /-- `byteAllocationView`: the generic allocation of a blob at the free
  pointer is exactly the existing allocation image. -/
  byteAllocation : ∀ (P : Params) (bs : List UInt8) (base : Nat) (free : Roadmap.Word)
    (fits : base + (MemoryShape.bytes bs.length).size ≤ free.val) (m : Phys),
    128 ≤ base → m.free = base → free.val = base + (MemoryShape.bytes bs.length).size →
    V.alloc P .bytes (.blob bs) m = some (base, m.withMemory (byteAllocationView bs base free fits m.memory))
  /-- `objectAllocationView`: every existing object allocation is a generic
  allocation of its shape's layout, at the same base and to the same image. -/
  objectAllocation : ∀ (P : Params) {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    {τ : Source.STy} (data : Source.Data D τ) (memory : τ.loc? = some .memory) (shape : MemoryShape)
    (shaped : HasMemoryShape data shape) (base : Nat) (free : Roadmap.Word) (after : p.free.val ≤ base)
    (fresh : ∀ a, (h.cells a).isSome → p.address a ≠ base) (fits : base + shape.size ≤ free.val)
    (m : Phys) (image : ByteView),
    objectAllocationView h p data memory shape shaped base free after fresh fits m.memory = some image →
    m.free = base → free.val = base + shape.size →
    ∃ t, (memoryShapeLayout shape).Fits t ∧
      V.alloc P (memoryShapeLayout shape) t m = some (base, m.withMemory image)
  /-- `enumeratedMemoryView`: every placed live object is readable at its
  address with its shape's layout, and `Placement.separate` is footprint
  disjointness. -/
  enumerated : ∀ (P : Params) {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (r image : ByteView) (m : Phys), enumeratedMemoryView p r = .ok image →
    (∀ a, (h.cells a).isSome → ∃ t, (memoryShapeLayout (p.shape a)).Fits t ∧
      V.geometry.read P (memoryShapeLayout (p.shape a)) ⟨.memory, p.address a, 0⟩
        (m.withMemory image) = some t) ∧
    (∀ a b, (h.cells a).isSome → (h.cells b).isSome → a ≠ b →
      Apart (V.geometry.cells P (memoryShapeLayout (p.shape a)) ⟨.memory, p.address a, 0⟩
          (m.withMemory image))
        (V.geometry.cells P (memoryShapeLayout (p.shape b)) ⟨.memory, p.address b, 0⟩
          (m.withMemory image)))

end Solidity.Goals.Shrink

namespace Solidity.Goals

open Solidity.Goal

/-- One recursive layout-indexed view with its laws and every per-shape instance. -/
@[goal Solidity.Yul.Layout.view_correct "yv1-yul-layout-view"]
def yulLayoutView : Prop :=
  ∃ V : Shrink.LayoutView, V.Laws ∧ V.Geometric ∧ V.Instances

/-- The Scalar pilot of `yulLayoutView` (H517): ONE recursive view and
allocator with the general laws over every layout, and the Scalar
correspondence of that same view. -/
@[goal Solidity.Yul.Layout.pilot_correct "yv1-yul-layout-view"]
def yulLayoutPilot : Prop :=
  ∃ V : Shrink.LayoutView, V.Laws ∧ V.ScalarPilot

end Solidity.Goals
