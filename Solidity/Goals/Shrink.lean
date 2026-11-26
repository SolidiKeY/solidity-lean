import Solidity.Yul.Layout.Shared.Vocabulary
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


mutual
/-- **The view**: one recursion over the layout description. -/
def Geometry.read (V : Geometry) (P : Params) : Layout → Loc → Phys → Option Tree
  | .scalar w, l, m => (V.scalar P w l m).map .leaf
  | .fixedArray e n, l, m => (V.readElems P e l n 0 m).map .node
  | .dynArray e, l, m => (V.readElems P e (V.data P l m) (V.length P l m) 0 m).map .node
  | .bytes, l, m => (V.blob P l m).map .blob
  | .struct fs, l, m => (V.readFields P fs l fs 0 m).map .node
  | .mapping v, l, m => some (.keyed fun k => V.read P v (V.key P l k) m)
/-- Elements `i, i+1, …` of a sequence of `count` elements. -/
def Geometry.readElems (V : Geometry) (P : Params) (e : Layout) (l : Loc) :
    Nat → Nat → Phys → Option (List Tree)
  | 0, _, _ => some []
  | count + 1, i, m => do
    let x ← V.read P e (V.elem P e l i) m
    let xs ← V.readElems P e l count (i + 1) m
    pure (x :: xs)
/-- Fields `i, …` of the struct `all`. -/
def Geometry.readFields (V : Geometry) (P : Params) (all : List Layout) (l : Loc) :
    List Layout → Nat → Phys → Option (List Tree)
  | [], _, _ => some []
  | f :: fs, i, m => do
    let x ← V.read P f (V.field P all l i) m
    let xs ← V.readFields P all l fs (i + 1) m
    pure (x :: xs)
end

mutual
/-- **The writer**, by the same recursion: a whole mapping is not assignable
(solc), a mismatched tree is refused (`none`, never a no-op). -/
def Geometry.write (V : Geometry) (P : Params) : Layout → Loc → Tree → Phys → Option Phys
  | .scalar w, l, .leaf v, m =>
    if 0 < w ∧ w ≤ 32 ∧ v < 256 ^ w then V.writeScalar P w l v m else none
  | .fixedArray e n, l, .node xs, m =>
    if xs.length = n ∧ n < 2 ^ 256 then V.writeElems P e l xs 0 m else none
  | .dynArray e, l, .node xs, m =>
    if xs.length < 2 ^ 256 then do
      let m₁ ← V.writeLength P l xs.length m
      V.writeElems P e (V.data P l m₁) xs 0 m₁
    else none
  | .bytes, l, .blob bs, m => V.writeBlob P l bs m
  | .struct fs, l, .node xs, m => V.writeFields P fs l fs xs 0 m
  | _, _, _, _ => none
def Geometry.writeElems (V : Geometry) (P : Params) (e : Layout) (l : Loc) :
    List Tree → Nat → Phys → Option Phys
  | [], _, m => some m
  | x :: xs, i, m => do
    let m₁ ← V.write P e (V.elem P e l i) x m
    V.writeElems P e l xs (i + 1) m₁
def Geometry.writeFields (V : Geometry) (P : Params) (all : List Layout) (l : Loc) :
    List Layout → List Tree → Nat → Phys → Option Phys
  | [], [], _, m => some m
  | f :: fs, x :: xs, i, m => do
    let m₁ ← V.write P f (V.field P all l i) x m
    V.writeFields P all l fs xs (i + 1) m₁
  | _, _, _, _ => none
end

mutual
/-- The footprint, by the same recursion: what a read may depend on and a
write may change. -/
def Geometry.cells (V : Geometry) (P : Params) : Layout → Loc → Phys → Cell → Prop
  | .scalar w, l, _, c => V.scalarCells P w l c
  | .fixedArray e n, l, m, c => V.elemCells P e l n 0 m c
  | .dynArray e, l, m, c => V.lengthCells P l c ∨ V.elemCells P e (V.data P l m) (V.length P l m) 0 m c
  | .bytes, l, m, c => V.lengthCells P l c ∨ V.blobCells P l m c
  | .struct fs, l, m, c => V.fieldCells P fs l fs 0 m c
  | .mapping v, l, m, c => ∃ k, V.cells P v (V.key P l k) m c
def Geometry.elemCells (V : Geometry) (P : Params) (e : Layout) (l : Loc) :
    Nat → Nat → Phys → Cell → Prop
  | 0, _, _, _ => False
  | count + 1, i, m, c => V.cells P e (V.elem P e l i) m c ∨ V.elemCells P e l count (i + 1) m c
def Geometry.fieldCells (V : Geometry) (P : Params) (all : List Layout) (l : Loc) :
    List Layout → Nat → Phys → Cell → Prop
  | [], _, _, _ => False
  | f :: fs, i, m, c => V.cells P f (V.field P all l i) m c ∨ V.fieldCells P all l fs (i + 1) m c
end

/-- Two footprints share no cell. -/
def Apart (a b : Cell → Prop) : Prop := ∀ c, ¬ (a c ∧ b c)

mutual
/-- **The written footprint**, by the same recursion, with lengths taken
from the written tree (not from a possibly clobbered state). -/
def Geometry.cellsT (V : Geometry) (P : Params) : Layout → Loc → Tree → Phys → Cell → Prop
  | .scalar w, l, _, _, c => V.scalarCells P w l c
  | .fixedArray e _, l, .node xs, m, c => V.elemCellsT P e l xs 0 m c
  | .dynArray e, l, .node xs, m, c => V.lengthCells P l c ∨ V.elemCellsT P e (V.data P l m) xs 0 m c
  | .bytes, l, _, m, c => V.lengthCells P l c ∨ V.blobCells P l m c
  | .struct fs, l, .node xs, m, c => V.fieldCellsT P fs l fs xs 0 m c
  | _, _, _, _, _ => False
def Geometry.elemCellsT (V : Geometry) (P : Params) (e : Layout) (l : Loc) :
    List Tree → Nat → Phys → Cell → Prop
  | [], _, _, _ => False
  | x :: xs, i, m, c => V.cellsT P e (V.elem P e l i) x m c ∨ V.elemCellsT P e l xs (i + 1) m c
def Geometry.fieldCellsT (V : Geometry) (P : Params) (all : List Layout) (l : Loc) :
    List Layout → List Tree → Nat → Phys → Cell → Prop
  | f :: fs, x :: xs, i, m, c => V.cellsT P f (V.field P all l i) x m c ∨
    V.fieldCellsT P all l fs xs (i + 1) m c
  | _, _, _, _, _ => False
end

mutual
/-- **Separation** (aliasing) of a written tree, by the same recursion:
distinct elements and fields, and a length word and its payload, occupy
disjoint cells (the recursive `finiteSeparated`). It is the premise of
read-after-write; a slot region that wraps onto itself violates it. -/
def Geometry.Separated (V : Geometry) (P : Params) : Layout → Loc → Tree → Phys → Prop
  | .fixedArray e _, l, .node xs, m => V.ElemsSeparated P e l xs 0 m
  | .dynArray e, l, .node xs, m => V.ElemsSeparated P e (V.data P l m) xs 0 m ∧
    Apart (V.lengthCells P l) (V.elemCellsT P e (V.data P l m) xs 0 m)
  | .bytes, l, _, m => Apart (V.lengthCells P l) (V.blobCells P l m)
  | .struct fs, l, .node xs, m => V.FieldsSeparated P fs l fs xs 0 m
  | _, _, _, _ => True
def Geometry.ElemsSeparated (V : Geometry) (P : Params) (e : Layout) (l : Loc) :
    List Tree → Nat → Phys → Prop
  | [], _, _ => True
  | x :: xs, i, m => V.Separated P e (V.elem P e l i) x m ∧
    Apart (V.cellsT P e (V.elem P e l i) x m) (V.elemCellsT P e l xs (i + 1) m) ∧
    V.ElemsSeparated P e l xs (i + 1) m
def Geometry.FieldsSeparated (V : Geometry) (P : Params) (all : List Layout) (l : Loc) :
    List Layout → List Tree → Nat → Phys → Prop
  | f :: fs, x :: xs, i, m => V.Separated P f (V.field P all l i) x m ∧
    Apart (V.cellsT P f (V.field P all l i) x m) (V.fieldCellsT P all l fs xs (i + 1) m) ∧
    V.FieldsSeparated P all l fs xs (i + 1) m
  | _, _, _, _ => True
end

mutual
/-- The trees a layout admits (the typing the laws preserve); lengths are
bounded as the existing views bound them (`< 2 ^ 256`). -/
def Layout.Fits : Layout → Tree → Prop
  | .scalar w, .leaf v => 0 < w ∧ w ≤ 32 ∧ v < 256 ^ w
  | .fixedArray e n, .node xs => xs.length = n ∧ n < 2 ^ 256 ∧ Layout.FitsAll e xs
  | .dynArray e, .node xs => xs.length < 2 ^ 256 ∧ Layout.FitsAll e xs
  | .bytes, .blob bs => bs.length < 2 ^ 256
  | .struct fs, .node xs => Layout.FitsFields fs xs
  | .mapping v, .keyed f => ∀ k t, f k = some t → Layout.Fits v t
  | _, _ => False
def Layout.FitsAll (e : Layout) : List Tree → Prop
  | [] => True
  | x :: xs => Layout.Fits e x ∧ Layout.FitsAll e xs
def Layout.FitsFields : List Layout → List Tree → Prop
  | [], [] => True
  | f :: fs, x :: xs => Layout.Fits f x ∧ Layout.FitsFields fs xs
  | _, _ => False
end

/-- No mapping anywhere: what can be assigned whole or allocated in memory. -/
def Layout.NoMapping : Layout → Prop
  | .scalar _ | .bytes => True
  | .fixedArray e _ | .dynArray e => e.NoMapping
  | .struct fs => ∀ f ∈ fs, f.NoMapping
  | .mapping _ => False

/-- The size of a finite tree (words and bytes), bounding its memory image. -/
def Tree.weight : Tree → Nat
  | .leaf _ => 1
  | .node cs => 1 + (cs.map Tree.weight).sum
  | .keyed _ => 0
  | .blob bs => 2 + bs.length

/-- The view with its allocator (the allocation choice is the bump allocator
the laws and the `byteAllocation`/`objectAllocation` instances pin). -/
structure LayoutView where
  geometry : Geometry
  alloc : Params → Layout → Tree → Phys → Option (Nat × Phys)

/-- **The laws**, proved once for every layout, location, tree, state and
parameters. -/
structure LayoutView.Laws (V : LayoutView) : Prop where
  /-- A read depends on its footprint only. -/
  local_read : ∀ P L l m m', (∀ c, V.geometry.cells P L l m c → m.byte c = m'.byte c) →
    V.geometry.read P L l m = V.geometry.read P L l m'
  /-- Read after write, for every fitting tree whose written footprint is separated. -/
  write_read : ∀ P L l t m m', L.Fits t → V.geometry.write P L l t m = some m' →
    V.geometry.Separated P L l t m' → V.geometry.read P L l m' = some t
  /-- A fitting mapping-free persistent/transient write succeeds. -/
  write_total : ∀ P L l t m, l.region ≠ .memory → L.NoMapping → L.Fits t →
    ∃ m', V.geometry.write P L l t m = some m'
  /-- An ill-typed write fails, never a no-op (as `heapPutConcrete_error`). -/
  illTyped : ∀ P L l t m, ¬ L.Fits t → V.geometry.write P L l t m = none
  /-- Frame: a write changes cells of the written footprint only. -/
  frame : ∀ P L l t m m', V.geometry.write P L l t m = some m' →
    ∀ c, ¬ V.geometry.cellsT P L l t m' c → m'.byte c = m.byte c
  /-- Allocation: the tree is readable at the returned address, at or above
  the old free pointer; the object's footprint lies below the new free
  pointer; slots, scratch and memory below the old free pointer (outside the
  free-pointer word) are unchanged. -/
  alloc_read : ∀ P L t m a m', L.Fits t → V.alloc P L t m = some (a, m') →
    V.geometry.read P L ⟨.memory, a, 0⟩ m' = some t ∧ m.free ≤ a ∧
    (∀ c, V.geometry.cells P L ⟨.memory, a, 0⟩ m' c → ∃ x, c = .mem x ∧ m.free ≤ x ∧ x < m'.free) ∧
    m'.storage = m.storage ∧ m'.transient = m.transient ∧
    (∀ x, x < m.free → (x < 64 ∨ 96 ≤ x) → m'.memory x = m.memory x)
  /-- A fitting mapping-free allocation whose size fits the address space
  succeeds from a free pointer past the reserved words (`[0,128)`: scratch,
  free pointer, zero slot; `ReservedOK`, `Placement.free_start`). -/
  alloc_total : ∀ P L t m, L.NoMapping → L.Fits t → 128 ≤ m.free →
    m.free + 64 * t.weight < 2 ^ 256 →
    ∃ a m', V.alloc P L t m = some (a, m')

/-- The shape of an existing heap object, as a layout: memory objects hold
words, nested references as pointer words (`HasMemoryShape`). -/
def memoryShapeLayout : MemoryShape → Layout
  | .bytes _ => .bytes
  | .array true _ => .dynArray (.scalar 32)
  | .array false n => .fixedArray (.scalar 32) n
  | .strct n => .struct (List.replicate n (.scalar 32))

/-- A slot region. -/
def Region.slotted : Region → Prop
  | .memory => False
  | _ => True

/-- **The geometry instances**: the placements and codecs of the existing
storage and memory encodings, so mappings, dynamic data, packing and
lengths are pinned, and the dirty-bit parameter has its effect. -/
structure LayoutView.Geometric (V : LayoutView) : Prop where
  /-- A packed field of a slot reads and writes as `Field.findWord`/`patchScalarSlot`. -/
  scalar : ∀ (P : Params) (r : Region) (f : Field) (slot : Roadmap.Word) (m : Phys), r.slotted →
    V.geometry.scalar P f.width ⟨r, slot.val, f.offset⟩ m = some (f.findWord (m.slots r slot)).val ∧
    (∀ v : f.Value, V.geometry.writeScalar P f.width ⟨r, slot.val, f.offset⟩ v.val m =
      some (m.withSlots r (patchScalarSlot (m.slots r) slot f v))) ∧
    (∀ c, V.geometry.scalarCells P f.width ⟨r, slot.val, f.offset⟩ c ↔
      ∃ b, c = .slot r slot b ∧ f.offset ≤ b ∧ b < f.offset + f.width)
  /-- A memory word reads and writes as `mload`/`mstore`; a narrower memory
  value is cleaned of its dirty high bits exactly when `cleanDirty`. -/
  memoryScalar : ∀ (P : Params) (w a : Nat) (m : Phys), 0 < w → w ≤ 32 →
    V.geometry.scalar P w ⟨.memory, a, 0⟩ m =
      some (if P.cleanDirty then mloadNat m.memory a % 256 ^ w else mloadNat m.memory a) ∧
    (∀ v, v < 256 ^ w → V.geometry.writeScalar P w ⟨.memory, a, 0⟩ v m =
      some (m.withMemory (mstore m.memory a (toWord v)))) ∧
    (∀ c, V.geometry.scalarCells P w ⟨.memory, a, 0⟩ c ↔ objectCells a 32 c)
  /-- A dynamic length is the slot's word / the memory header word. -/
  length : ∀ (P : Params) (r : Region) (w n : Nat) (m : Phys),
    V.geometry.length P ⟨r, w, 0⟩ m = (if r = .memory then mloadNat m.memory w else (m.slots r (toWord w)).val) ∧
    V.geometry.writeLength P ⟨r, w, 0⟩ n m =
      some (if r = .memory then m.withMemory (mstore m.memory w (toWord n))
        else m.withSlots r (saveSlot (m.slots r) (toWord w) (toWord n))) ∧
    (∀ c, V.geometry.lengthCells P ⟨r, w, 0⟩ c ↔
      if r = .memory then objectCells w 32 c else ∃ b, c = .slot r (toWord w) b ∧ b < 32)
  /-- Dynamic data starts at `keccak(slot)` in storage (`Storage.Loc.data`)
  and after the header word in memory. -/
  data : ∀ (P : Params) (r : Region) (w : Nat) (m : Phys),
    V.geometry.data P ⟨r, w, 0⟩ m =
      if r = .memory then ⟨.memory, w + 32, 0⟩
      else ⟨r, (physicalSlot P.hash (.data (.root w) 0)).val, 0⟩
  /-- A mapping value lives at `keccak(key . slot)` (`Storage.Loc.hash`). -/
  key : ∀ (P : Params) (r : Region) (w : Nat) (k : Roadmap.Word), r.slotted →
    V.geometry.key P ⟨r, w, 0⟩ k = ⟨r, (physicalSlot P.hash (.hash k.val (.root w) 0)).val, 0⟩
  /-- Elements of narrow scalars pack `32 / w` per slot; memory elements are words. -/
  elem : ∀ (P : Params) (r : Region) (w base i : Nat), 0 < w → w ≤ 32 →
    V.geometry.elem P (.scalar w) ⟨r, base, 0⟩ i =
      if r = .memory then ⟨.memory, base + 32 * i, 0⟩
      else ⟨r, (toWord (base + i / (32 / w))).val, i % (32 / w) * w⟩
  /-- Storage elements of an aggregate start every `e.slots` slots. -/
  elemAggregate : ∀ (P : Params) (r : Region) (e : Layout) (base i : Nat), r.slotted →
    (∀ w, e ≠ .scalar w) → V.geometry.elem P e ⟨r, base, 0⟩ i = ⟨r, (toWord (base + i * e.slots)).val, 0⟩
  /-- Struct members pack by `packedStart`, aggregates from a fresh slot;
  memory scalar members are words. -/
  field : ∀ (P : Params) (r : Region) (fs : List Layout) (base i : Nat), i < fs.length →
    (r.slotted → V.geometry.field P fs ⟨r, base, 0⟩ i =
      ⟨r, (toWord (base + Layout.memberStart fs 0 i / 32)).val, Layout.memberStart fs 0 i % 32⟩) ∧
    (r = .memory → (∀ f ∈ fs, ∃ w, f = .scalar w) →
      V.geometry.field P fs ⟨.memory, base, 0⟩ i = ⟨.memory, base + 32 * i, 0⟩)

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

/-- **The Scalar pilot correspondence** (H517 measured pilot, before migration):
the scalar leaf of the recursive view is the existing packed scalar family.
`scalar` and `memoryScalar` restate `Geometric.scalar` and
`Geometric.memoryScalar` verbatim; `scalarPathRead` and `scalarPathWrite` tie
the recursive `Geometry.read`/`Geometry.write` at `.scalar f.width` to
`scalarPathView` and `encodeScalarPath` (so `patchScalarSlot`) in both slot
regions. Those two follow from `scalar`; they are stated so a consumer of the
existing family needs no unfolding. Element, field, key and data placements
are not pinned here, so the `Laws` alone do not exclude aliased storage
aggregates; later shapes are `Geometric`/`Instances` work (yv2/yv3). -/
structure LayoutView.ScalarPilot (V : LayoutView) : Prop where
  /-- A packed field of a slot reads and writes as `Field.findWord`/`patchScalarSlot`. -/
  scalar : ∀ (P : Params) (r : Region) (f : Field) (slot : Roadmap.Word) (m : Phys), r.slotted →
    V.geometry.scalar P f.width ⟨r, slot.val, f.offset⟩ m = some (f.findWord (m.slots r slot)).val ∧
    (∀ v : f.Value, V.geometry.writeScalar P f.width ⟨r, slot.val, f.offset⟩ v.val m =
      some (m.withSlots r (patchScalarSlot (m.slots r) slot f v))) ∧
    (∀ c, V.geometry.scalarCells P f.width ⟨r, slot.val, f.offset⟩ c ↔
      ∃ b, c = .slot r slot b ∧ f.offset ≤ b ∧ b < f.offset + f.width)
  /-- A memory word reads and writes as `mload`/`mstore`; a narrower memory
  value is cleaned of its dirty high bits exactly when `cleanDirty`. -/
  memoryScalar : ∀ (P : Params) (w a : Nat) (m : Phys), 0 < w → w ≤ 32 →
    V.geometry.scalar P w ⟨.memory, a, 0⟩ m =
      some (if P.cleanDirty then mloadNat m.memory a % 256 ^ w else mloadNat m.memory a) ∧
    (∀ v, v < 256 ^ w → V.geometry.writeScalar P w ⟨.memory, a, 0⟩ v m =
      some (m.withMemory (mstore m.memory a (toWord v)))) ∧
    (∀ c, V.geometry.scalarCells P w ⟨.memory, a, 0⟩ c ↔ objectCells a 32 c)
  /-- `scalarPathView`, at every path, codec, store, slot and slot region, is
  the recursive view of `.scalar f.width` at the field's slot and offset. -/
  scalarPathRead : ∀ (P : Params) {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (r : Region) (m : Phys), r.slotted →
    (scalarPathView p c slot s (m.slots r) ↔
      (s.read p).map (fun v => Tree.leaf (c.encode v).val) =
        V.geometry.read P (.scalar f.width) ⟨r, slot.val, f.offset⟩ m)
  /-- `encodeScalarPath` (so `patchScalarSlot`) is the recursive writer of the
  path's encoded value: the region's slots patched, the other region and
  memory kept; `none` exactly when the path holds no value. -/
  scalarPathWrite : ∀ (P : Params) {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (r : Region) (m : Phys), r.slotted →
    (s.read p).bind (fun v =>
        V.geometry.write P (.scalar f.width) ⟨r, slot.val, f.offset⟩ (.leaf (c.encode v).val) m) =
      (encodeScalarPath p c slot s (m.slots r)).map (m.withSlots r)

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
