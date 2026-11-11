import Solidity.Tools.Goal
import Solidity.Correctness.Lowering.Checker.Contract
import Solidity.Lowering.V07.Scalar
import Solidity.Semantics.RunFuel
import Solidity.Lowering.P8.FrozenInterface
import Solidity.Roadmap.G49Final.PassCorrectAdapters
import Solidity.Backend.AbiWorld.PublicCompilerTotal
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

* `yulLayoutView` (`Solidity.Yul.Layout.view_correct`): ONE view defined by
  structural recursion over an inductive layout description (`Shrink.Layout`),
  with read-after-write, frame, failure and allocation laws proved once, and
  an instance relation that pins the view to every existing per-shape view
  definition of `Solidity/Yul/Views` (inventory below).
* `loweringBySimulation` (`Solidity.Correctness.Lowering.Sim.lowering_producer`):
  ONE forward simulation diagram over the actual production lowering
  (`lowerLoops` then `lowerReturns`, as `calleeBody` sequences them, and the
  standalone `lowerLoops none` sites) followed by the actual elaborator
  (`elabStmtsP`, `SProg.chain`), with its fresh-name state, on t0's accepted
  fragment (`PublicCompilerTotal.ProgOk []`); from that same diagram, for every
  source/intrinsic pair bound to actual Source sessions, a frozen
  `Roadmap.Lowering S I` and a `G49Final.PassCorrect` per program whose
  data fields (environment map, resource transport) are the diagram's.

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

/-- Where a value lives. -/
inductive Region where
  | storage
  | transient
  | memory
  deriving DecidableEq, Repr

/-- The layout description: the one inductive type the view recurses on.
`scalar w` is a value of `w` bytes (packed when `w < 32` in storage). -/
inductive Layout where
  | scalar (width : Nat)
  | fixedArray (elem : Layout) (length : Nat)
  | dynArray (elem : Layout)
  | bytes
  | struct (fields : List Layout)
  | mapping (value : Layout)

/-- A location: a region, a slot or memory address, a byte offset in the slot. -/
structure Loc where
  region : Region
  word : Nat
  offset : Nat

/-- The physical machine the views read: persistent and transient slots, memory. -/
structure Phys where
  storage : SlotView
  transient : SlotView
  memory : ByteView

/-- The abstract value a layout holds. -/
inductive Tree where
  | leaf (value : Nat)
  | node (children : List Tree)
  | keyed (entry : Roadmap.Word → Option Tree)
  | blob (bytes : List UInt8)

/-- One physical byte: a byte of a slot (least significant first) or of memory. -/
inductive Cell where
  | slot (region : Region) (word : Nat) (byte : Nat)
  | mem (address : Nat)

/-- A word of `2 ^ 256`, from a natural number. -/
def toWord (n : Nat) : Roadmap.Word := ⟨n % 2 ^ 256, Nat.mod_lt _ (by decide)⟩

/-- The byte a cell holds. -/
def Phys.byte (m : Phys) : Cell → Nat
  | .slot .storage w b => (m.storage (toWord w)).val / 256 ^ b % 256
  | .slot .transient w b => (m.transient (toWord w)).val / 256 ^ b % 256
  | .slot .memory _ _ => 0
  | .mem a => (m.memory a).toNat

/-- The free-memory pointer (`mload(0x40)`). -/
def Phys.free (m : Phys) : Nat := mloadNat m.memory 64

/-- The slot view replaced, memory and the other slots left as they are. -/
def Phys.withStorage (m : Phys) (s : SlotView) : Phys := { m with storage := s }

/-- The transient slot view replaced. -/
def Phys.withTransient (m : Phys) (s : SlotView) : Phys := { m with transient := s }

/-- The memory image replaced, slots left as they are. -/
def Phys.withMemory (m : Phys) (b : ByteView) : Phys := { m with memory := b }

/-- The slots of a slot region. -/
def Phys.slots (m : Phys) : Region → SlotView
  | .transient => m.transient
  | _ => m.storage

/-- The slots of a slot region replaced. -/
def Phys.withSlots (m : Phys) : Region → SlotView → Phys
  | .transient, s => m.withTransient s
  | _, s => m.withStorage s

/-- The pipeline/codec parameters every law quantifies over: the slot hash
(as `physicalSlot` reads it), whether dirty high bits of a narrow memory
value are cleaned on read, and the solc pipeline. -/
structure Params where
  hash : Storage.Pre → Nat
  cleanDirty : Bool
  pipeline : Roadmap.Pipeline

/-- The per-constructor geometry of the view: leaf codecs and placements.
The view and its writer are NOT fields: they are `Geometry.read` and
`Geometry.write`, structural recursions over `Layout`. -/
structure Geometry where
  scalar : Params → Nat → Loc → Phys → Option Nat
  writeScalar : Params → Nat → Loc → Nat → Phys → Option Phys
  elem : Params → Layout → Loc → Nat → Loc
  field : Params → List Layout → Loc → Nat → Loc
  length : Params → Loc → Phys → Nat
  writeLength : Params → Loc → Nat → Phys → Option Phys
  data : Params → Loc → Phys → Loc
  key : Params → Loc → Roadmap.Word → Loc
  blob : Params → Loc → Phys → Option (List UInt8)
  writeBlob : Params → Loc → List UInt8 → Phys → Option Phys
  /-- The cells a scalar, a dynamic length word and a blob payload read. -/
  scalarCells : Params → Nat → Loc → Cell → Prop
  lengthCells : Params → Loc → Cell → Prop
  blobCells : Params → Loc → Phys → Cell → Prop

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
  | .scalar w, l, .leaf v, m => if v < 256 ^ w then V.writeScalar P w l v m else none
  | .fixedArray e n, l, .node xs, m =>
    if xs.length = n then V.writeElems P e l xs 0 m else none
  | .dynArray e, l, .node xs, m => do
    let m₁ ← V.writeLength P l xs.length m
    V.writeElems P e (V.data P l m₁) xs 0 m₁
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
/-- **Separation** (aliasing), by the same recursion: distinct elements,
fields, keys, a length word and its payload occupy disjoint cells (the
recursive `finiteSeparated`). It is a premise of read-after-write only. -/
def Geometry.Separated (V : Geometry) (P : Params) : Layout → Loc → Phys → Prop
  | .scalar _, _, _ => True
  | .fixedArray e n, l, m => V.ElemsSeparated P e l n m
  | .dynArray e, l, m => V.ElemsSeparated P e (V.data P l m) (V.length P l m) m ∧
    Apart (V.lengthCells P l) (V.elemCells P e (V.data P l m) (V.length P l m) 0 m)
  | .bytes, l, m => Apart (V.lengthCells P l) (V.blobCells P l m)
  | .struct fs, l, m => V.FieldsSeparated P fs l fs 0 m
  | .mapping v, l, m => (∀ k, V.Separated P v (V.key P l k) m) ∧
    ∀ k k', k ≠ k' → Apart (V.cells P v (V.key P l k) m) (V.cells P v (V.key P l k') m)
def Geometry.ElemsSeparated (V : Geometry) (P : Params) (e : Layout) (l : Loc) (n : Nat)
    (m : Phys) : Prop :=
  (∀ i, i < n → V.Separated P e (V.elem P e l i) m) ∧
  ∀ i j, i < n → j < n → i ≠ j → Apart (V.cells P e (V.elem P e l i) m) (V.cells P e (V.elem P e l j) m)
def Geometry.FieldsSeparated (V : Geometry) (P : Params) (all : List Layout) (l : Loc) :
    List Layout → Nat → Phys → Prop
  | [], _, _ => True
  | f :: fs, i, m => V.Separated P f (V.field P all l i) m ∧
    Apart (V.cells P f (V.field P all l i) m) (V.fieldCells P all l fs (i + 1) m) ∧
    V.FieldsSeparated P all l fs (i + 1) m
end

mutual
/-- The trees a layout admits (the typing the laws preserve); lengths are
bounded as the existing views bound them (`< 2 ^ 256`). -/
def Layout.Fits : Layout → Tree → Prop
  | .scalar w, .leaf v => v < 256 ^ w
  | .fixedArray e n, .node xs => xs.length = n ∧ Layout.FitsAll e xs
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
  /-- Read after write, for every fitting tree whose result is separated. -/
  write_read : ∀ P L l t m m', L.Fits t → V.geometry.write P L l t m = some m' →
    V.geometry.Separated P L l m' → V.geometry.read P L l m' = some t
  /-- A fitting mapping-free persistent/transient write succeeds. -/
  write_total : ∀ P L l t m, l.region ≠ .memory → L.NoMapping → L.Fits t →
    ∃ m', V.geometry.write P L l t m = some m'
  /-- An ill-typed write fails, never a no-op (as `heapPutConcrete_error`). -/
  illTyped : ∀ P L l t m, ¬ L.Fits t → V.geometry.write P L l t m = none
  /-- Frame: a write changes cells of its footprint (before or after) only. -/
  frame : ∀ P L l t m m', V.geometry.write P L l t m = some m' →
    ∀ c, ¬ V.geometry.cells P L l m' c → ¬ V.geometry.cells P L l m c → m'.byte c = m.byte c
  /-- Allocation: the tree is readable at the returned address, at or above
  the old free pointer; the object's footprint lies below the new free
  pointer; slots, scratch and memory below the old free pointer (outside the
  free-pointer word) are unchanged. -/
  alloc_read : ∀ P L t m a m', L.Fits t → V.alloc P L t m = some (a, m') →
    V.geometry.read P L ⟨.memory, a, 0⟩ m' = some t ∧ m.free ≤ a ∧
    (∀ c, V.geometry.cells P L ⟨.memory, a, 0⟩ m' c → ∃ x, c = .mem x ∧ m.free ≤ x ∧ x < m'.free) ∧
    m'.storage = m.storage ∧ m'.transient = m.transient ∧
    (∀ x, x < m.free → (x < 64 ∨ 96 ≤ x) → m'.memory x = m.memory x)
  /-- A fitting mapping-free allocation whose size fits the address space succeeds. -/
  alloc_total : ∀ P L t m, L.NoMapping → L.Fits t → m.free + 64 * t.weight < 2 ^ 256 →
    ∃ a m', V.alloc P L t m = some (a, m')

/-- The shape of an existing heap object, as a layout: memory objects hold
words, nested references as pointer words (`HasMemoryShape`). -/
def memoryShapeLayout : MemoryShape → Layout
  | .bytes _ => .bytes
  | .array true _ => .dynArray (.scalar 32)
  | .array false n => .fixedArray (.scalar 32) n
  | .strct n => .struct (List.replicate n (.scalar 32))

/-- The footprint `[base, base + size)` of a memory object. -/
def objectCells (base size : Nat) : Cell → Prop
  | .mem x => base ≤ x ∧ x < base + size
  | .slot _ _ _ => False

/-- The byte starts of packed scalar members of the given widths from
`cursor`, by the existing packing rule (`packedStart`, PackedAggregates.lean:54). -/
def packedStarts : List Nat → Nat → List Nat
  | [], _ => []
  | w :: ws, cursor => packedStart cursor w :: packedStarts ws (packedStart cursor w + w)

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
      ∃ b, c = .slot r slot.val b ∧ f.offset ≤ b ∧ b < f.offset + f.width)
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
      if r = .memory then objectCells w 32 c else ∃ b, c = .slot r w b ∧ b < 32)
  /-- Dynamic data starts at `keccak(slot)` in storage (`Storage.Loc.data`)
  and after the header word in memory. -/
  data : ∀ (P : Params) (r : Region) (w : Nat) (m : Phys),
    V.geometry.data P ⟨r, w, 0⟩ m =
      if r = .memory then ⟨.memory, w + 32, 0⟩
      else ⟨r, (physicalSlot P.hash (.data (.root w) 0)).val, 0⟩
  /-- A mapping value lives at `keccak(key . slot)` (`Storage.Loc.hash`). -/
  key : ∀ (P : Params) (r : Region) (w : Nat) (k : Roadmap.Word),
    V.geometry.key P ⟨r, w, 0⟩ k = ⟨r, (physicalSlot P.hash (.hash k.val (.root w) 0)).val, 0⟩
  /-- Elements of narrow scalars pack `32 / w` per slot; memory elements are words. -/
  elem : ∀ (P : Params) (r : Region) (w base i : Nat), 0 < w → w ≤ 32 →
    V.geometry.elem P (.scalar w) ⟨r, base, 0⟩ i =
      if r = .memory then ⟨.memory, base + 32 * i, 0⟩
      else ⟨r, base + i / (32 / w), i % (32 / w) * w⟩
  /-- Struct members of scalars pack by `packedStart`; memory members are words. -/
  field : ∀ (P : Params) (r : Region) (ws : List Nat) (base i : Nat), i < ws.length →
    V.geometry.field P (ws.map Layout.scalar) ⟨r, base, 0⟩ i =
      if r = .memory then ⟨.memory, base + 32 * i, 0⟩
      else ⟨r, base + (packedStarts ws 0).getD i 0 / 32, (packedStarts ws 0).getD i 0 % 32⟩

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
    m.free = base → free.val = base + (MemoryShape.bytes bs.length).size →
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

/-! ## Lowering by simulation -/

namespace Lowering

open Solidity.Correctness.Lowering.Checker (Snapshot Input Output ElaborationReceipt)
open Solidity.Lowering.V07 (ContextMap IntValueRel integerPrim)
open Solidity.Roadmap (SourceSpec IntrinsicSpec Artifact Prefix Event Outcome SessionEnv)

variable [FreshNames]

/-- The production lowering exactly as its callers sequence it: a function
body (`calleeBody`, Arms.lean:828-829) lowers its loops then its returns into
the return slots; a standalone loop (Arms.lean:1522, 1926) lowers its loops
with no slots. -/
def lowerAt : Option (List String) → List RawStmt → ElabM (List RawStmt)
  | none, raw => lowerLoops none raw
  | some rs, raw => do
    let lowered ← lowerLoops (some rs) raw
    ElabM.lift (lowerReturns rs lowered)

/-- A callee's return slots, renamed as `calleeBody` renames them. -/
def returnSlots (d : FunDecl) (ρ : List (String × String)) : List String :=
  d.rets.map fun (n, _) => (Semantics.lookupBy n ρ).getD n

/-- What `calleeBody` does after lowering (Arms.lean:830-841). -/
def callerTail (C : Contract) (d : FunDecl) (ρ : List (String × String)) (ctor selfFrame : Bool)
    (Γf : ECtx) (body : List RawStmt) : ElabM (List RawStmt) := do
  let frame := if C.evalOrder.modifierFrames then some (d, ρ) else none
  let body ← wrapMods C body frame (d.mods.map fun m => { m with args := m.args.map (·.rename ρ) })
  let body := (if ctor then C.inits.map fun (x, e) => RawStmt.assign (.name x) e else []) ++ body
  let selfValue := (← read).selfValue
  let body := if selfFrame then body.map (RawStmt.selfFrame selfValue) else body
  ElabM.lift (freshenBlocks (C.vars.map (·.1)) (Γf.map (·.1)) body)

/-- **The callers are bound**: the actual function-body producer is renaming,
then `lowerAt`, then the rest of `calleeBody`. -/
def CallerBound : Prop :=
  ∀ (C : Contract) (d : FunDecl) (ρ : List (String × String)) (ctor selfFrame : Bool) (Γf : ECtx),
    calleeBody C d ρ ctor selfFrame Γf = (do
      let body ← renameStmts ρ d.body
      let body ← lowerAt (some (returnSlots d ρ)) body
      callerTail C d ρ ctor selfFrame Γf body)

/-- Where the production lowering runs: a standalone loop
(`elabStmtsP (← lowerLoops none [s])`, Arms.lean:1522, 1926), or an inlined
callee's body (`inlinedBody`, Arms.lean:846-865: `calleeBody`, then the
locals reset to `Γf` and its body elaborated under the callee scope). The
shared-memo branch of `inlinedBody` reuses an earlier body and runs no
lowering; it is the earlier run's association. -/
inductive Site where
  | loop
  | callee (d : FunDecl) (ρ : List (String × String)) (ctor selfFrame : Bool) (Γf : ECtx)
      (funs : List (Name × FunDecl)) (k₀ : Nat)

/-- A source body with its production input and its site. -/
structure Body where
  E : Source.Env
  returns : List Source.STy
  modifier : Bool
  control : Source.SCtx
  ctx : Source.RCtx
  input : Input E returns modifier control ctx
  site : Site

/-- An emitted program with its production state. -/
structure Emitted where
  C : Contract
  Γ : Ctx
  output : Output C Γ

/-- The actual producer at the site ran on the input, from its scope and full
state, to the output's raw statements and state: `lowerAt none` for a loop,
the whole `calleeBody` (renaming, `lowerAt`, modifiers, initializers,
self-frame, freshening) for a callee, whose raw input is its declared body. -/
def Lowered (b : Body) (u : Emitted) : Prop :=
  match b.site with
  | .loop =>
    b.input.returnSlots = none ∧
    (((lowerAt none b.input.raw).run b.input.scope).run b.input.before.locals).run
      b.input.before.memo = .ok ((u.output.raw, u.output.afterLower.locals), u.output.afterLower.memo)
  | .callee d ρ ctor selfFrame Γf _ _ =>
    b.input.raw = d.body ∧ b.input.returnSlots = some (returnSlots d ρ) ∧
    (((calleeBody u.C d ρ ctor selfFrame Γf).run b.input.scope).run b.input.before.locals).run
      b.input.before.memo = .ok ((u.output.raw, u.output.afterLower.locals), u.output.afterLower.memo)

/-- The scope `inlinedBody` elaborates a callee's body under (Arms.lean:858-860). -/
def calleeScope (sc : ElabScope) (funs : List (Name × FunDecl)) (selfFrame : Bool) (k₀ k₁ : Nat) :
    ElabScope :=
  { sc with funs := funs, top := false, selfFrame := selfFrame, unchecked := false,
            inlined := (k₀, k₁) :: sc.inlined }

/-- The elaboration's state and scope are exactly the caller's: the same for
a standalone loop; for a callee, the locals reset to `Γf` with the counter
kept, and the scope `inlinedBody` sets. -/
def Threaded (b : Body) (u : Emitted) : Prop :=
  u.output.beforeElab.memo = u.output.afterLower.memo ∧
  match b.site with
  | .loop => u.output.elabScope = b.input.scope ∧ u.output.beforeElab.locals = u.output.afterLower.locals
  | .callee _ _ _ selfFrame Γf funs k₀ =>
    u.output.beforeElab.locals = (Γf, u.output.afterLower.locals.2) ∧
    u.output.elabScope = calleeScope b.input.scope funs selfFrame k₀ u.output.afterLower.locals.2

/-- **Production association**: the actual producer, the actual elaboration
(`elabStmtsP`, `SProg.chain`), the state threaded between them. -/
def Production (b : Body) (u : Emitted) : Prop :=
  Lowered b u ∧ ElaborationReceipt u.output ∧ Threaded b u

/-- Freshness (a conclusion, never a premise): the fresh counter only grows;
a loop's lowering also leaves the scope's locals and the memo untouched. -/
def LowerFresh (b : Body) (u : Emitted) : Prop :=
  b.input.before.locals.2 ≤ u.output.afterLower.locals.2 ∧
  (b.site = .loop → u.output.afterLower.locals.1 = b.input.before.locals.1 ∧
    u.output.afterLower.memo = b.input.before.memo)

/-- t0's accepted fragment (`Goals/Total.lean`), read on the emitted program. -/
def Accepted (u : Emitted) : Prop :=
  Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] u.output.program.2

/-- The actual Source run of the resolved statement at horizon `n`. -/
def sourceRun (b : Body) (G : Source.Glob b.E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph b.E)) (s : Source.EMState b.E b.ctx) :=
  (Source.execS G F n nps ph b.input.resolved s.1).run (.nil, s.2)

/-- Halts correspond: a revert keeps its data; a panic's data is the target's
`panic` (the intrinsic halt records no code: this observation is lossy and
the session-level `Cert` compares the exact data); a stuck or timed-out
source matches nothing. (`exhausted` is a storage push past its bound,
outside t0's fragment, which has no `push`.) -/
def HaltMatch : Source.Halt → THalt → Prop
  | .revert d, h => h = THalt.ofData d ∨ (h = .panic ∧ ∃ c, d = Source.panicData c)
  | .stuck _, _ => False
  | .timeout, _ => False

/-- **The one simulation**: its horizon transport, its association of a
resolved source with an actual production run, and its invariant (value and
global relations). -/
structure Diagram where
  fuel : Nat → Nat
  Assoc : (b : Body) → (u : Emitted) → ContextMap b.ctx u.Γ → Prop
  valRel : {D : Source.Layout} → {C : Contract} → {H : HTy} →
    (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C H → Prop
  globRel : {E : Source.Env} → {C : Contract} → {Γ : Ctx} → Source.St E → State C Γ → Prop

/-- Final matching of a source result and a target result: normal completion
and a lowered `return` reach a target state related by the invariant, along
the emitted program's context extension; halts correspond by `HaltMatch`;
a `break`/`continue` escaping the body, a stuck run or a timeout match nothing. -/
def Diagram.Final (D : Diagram) {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ Γ' : Ctx}
    {H : HTy} (m : ContextMap srcΓ Γ) (emb : Thin Γ Γ')
    (src : Except Source.Halt (Source.Out E.layout srcΓ srcΓ) ×
      (Source.Locals E.layout [] × Source.St E))
    (tgt : TRes (Out C H Γ')) : Prop :=
  match src.1, tgt with
  | .ok (.normal ls), .ok o =>
    (m.wk emb).Related (fun τ u => D.valRel τ u) ls o.st.env ∧ D.globRel src.2.2 o.st
  | .ok (.ret ls), .ok o =>
    (m.wk emb).Related (fun τ u => D.valRel τ u) ls o.st.env ∧ D.globRel src.2.2 o.st
  | .error h, .error t => HaltMatch h t
  | _, _ => False

/-- **The diagram's obligations**, for every actual production run on t0's
fragment that the diagram associates with a resolved source:

* the value relation reflects Booleans and integers (`IntValueRel`);
* initial matching is total: every source state has a related target state
  (so neither relation can be empty);
* at every source horizon that completes, the matching final target result
  at the transported fuel (forward diagram; a source timeout is stuttering);
* the transport is monotone (progress) and completed source runs are stable
  under larger horizons (Source determinacy, which `back` needs);
* every completed target run is matched by some completed source run
  (backward diagram: nondeterminism is not dropped, determinacy is proved);
* the producer's fresh state is sound (`LowerFresh`). -/
def Diagram.Simulates (D : Diagram) : Prop :=
  (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (v : Source.Val Dl .bool) (b : Bool),
    D.valRel (C := C) (H := H) .bool (.val .bool) v b → v = .bool b) ∧
  (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (t : Source.IntTy) (v : Source.Val Dl (.int t))
    (x : (integerPrim t).Denote), D.valRel (C := C) (H := H) (.int t) (.val (integerPrim t)) v x →
      IntValueRel t v x) ∧
  (∀ n n', n ≤ n' → D.fuel n ≤ D.fuel n') ∧
  ∀ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
    Production b u → Accepted u → D.Assoc b u m →
    LowerFresh b u ∧
    (∀ src : Source.EMState b.E b.ctx, ∃ tgt : State u.C u.Γ,
      m.Related (fun τ v => D.valRel τ v) src.1 tgt.env ∧ D.globRel src.2 tgt) ∧
    ∃ emb : Thin u.Γ u.output.program.1,
    ∀ (G : Source.Glob b.E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph b.E))
      (src : Source.EMState b.E b.ctx) (tgt : State u.C u.Γ),
      m.Related (fun τ v => D.valRel τ v) src.1 tgt.env → D.globRel src.2 tgt →
      (∀ n, (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
        D.Final m emb (sourceRun b G F n nps ph src) (u.output.program.2.runF (D.fuel n) tgt)) ∧
      (∀ n n', n ≤ n' → (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
        sourceRun b G F n' nps ph src = sourceRun b G F n nps ph src) ∧
      (∀ n, u.output.program.2.runF n tgt ≠ .error .diverge →
        ∃ j, D.Final m emb (sourceRun b G F j nps ph src) (u.output.program.2.runF n tgt))

/-- **Coverage of t0's fragment**: every actual production run whose emitted
program is in the fragment has a resolved source, at the same site and with
the same raw input, slots, scope and state, that the diagram associates with
it. (No raw-to-resolved function exists at the base; see the limitations.) -/
def Diagram.Total (D : Diagram) : Prop :=
  ∀ (b : Body) (u : Emitted), Production b u → Accepted u →
    ∃ b' : Body, b'.site = b.site ∧ b'.input.raw = b.input.raw ∧
      b'.input.returnSlots = b.input.returnSlots ∧ b'.input.scope = b.input.scope ∧
      b'.input.before = b.input.before ∧ ∃ m, D.Assoc b' u m

/-- The binding of a source/intrinsic pair to the actual programs: a
resolution's Source program (the frozen P8a origins) whose failure-free
prefixes are actual `Source.sessionAt` sessions; its production bodies (the
resolved-source association), each produced inside t0's fragment; and the
emitted programs of a world, whose sessions the world's semantics reads
through the intrinsic session reference `targetSession` (no actual intrinsic
session semantics exists at the base: an explicit parameter, as P8a's
`OperationalReference`). -/
structure Binding (S : SourceSpec) (I : IntrinsicSpec) where
  origins : Solidity.Lowering.P8.P8a.SourceOrigins S
  program : S.lang.Prog → Solidity.Lowering.P8.P8a.SourceProgram
  program_meaning : ∀ r w p art, program (S.meaning r w p art) = origins.meaning r w p art
  horizon : S.lang.Res → Nat
  source_exact : ∀ prog e res, S.NoFailure res →
    S.lang.sem prog e res = Source.sessionAt (program prog).2 (S.session e) (horizon res)
  bodies : S.Resolved → List Body
  bodies_env : ∀ r w p art, ∀ b ∈ bodies r, b.E = (origins.meaning r w p art).1
  produced : ∀ r, S.WellFormed r → S.InProfile r → ∀ b ∈ bodies r,
    ∃ u : Emitted, Production b u ∧ Accepted u
  units : I.World → List Emitted
  targetSession : List Emitted → SessionEnv → I.lang.Res → Prefix Event Outcome
  target_exact : ∀ w e res,
    I.lang.sem (I.ofWorld w) e res = targetSession (units w) (I.session e) res

/-- **Both carriers from the same diagram**: a frozen `Lowering S I` whose
worlds are exactly the production outputs of the resolution's bodies, each
associated by the diagram, whose environment map is the exact session
environment; and, for every program, a `PassCorrect` between the actual
behaviours with the SAME environment map and resource transport (all
`Cert`/`PassCorrect` fields, forward and back, are retained by their types). -/
def Diagram.Lifts (D : Diagram) {S : SourceSpec} {I : IntrinsicSpec} (B : Binding S I) : Prop :=
  ∃ L : Solidity.Roadmap.Lowering S I,
    (∀ e, L.pass.envAbs e = S.ofSession (I.session e)) ∧
    (∀ r w p art, (B.units (L.lower r w p art)).length = (B.bodies r).length ∧
      ∀ bu ∈ (B.bodies r).zip (B.units (L.lower r w p art)),
        Production bu.1 bu.2 ∧ ∃ m, D.Assoc bu.1 bu.2 m) ∧
    ∃ pc : (r : S.Resolved) → (w : S.WellFormed r) → (p : S.InProfile r) → (art : Artifact) →
        Solidity.Roadmap.G49Final.PassCorrect
          (Solidity.Roadmap.G49Final.Behaviour.ofLang S.lang (S.meaning r w p art))
          (Solidity.Roadmap.G49Final.Behaviour.ofLang I.lang (I.ofWorld (L.lower r w p art))),
      ∀ r w p art, (pc r w p art).envAbs = L.pass.envAbs ∧
        (pc r w p art).need = L.cert.need (S.meaning r w p art) (L.dom r w p art)

/-- A naming policy whose fresh names are distinct and parse back. -/
def FreshNames.Lawful (N : FreshNames) : Prop :=
  (∀ s n, N.parse (N.name s n) = some (s, n)) ∧
  ∀ s n s' n', N.name s n = N.name s' n' → s = s' ∧ n = n'

end Lowering

end Solidity.Goals.Shrink

namespace Solidity.Goals

open Solidity.Goal

/-- One recursive layout-indexed view with its laws and every per-shape instance. -/
@[goal Solidity.Yul.Layout.view_correct "yv1-yul-layout-view"]
def yulLayoutView : Prop :=
  ∃ V : Shrink.LayoutView, V.Laws ∧ V.Geometric ∧ V.Instances

/-- Production lowering on t0's fragment by one simulation, lifted to a frozen
`Lowering` and a direct `PassCorrect` from the same diagram. -/
@[goal Solidity.Correctness.Lowering.Sim.lowering_producer "ls3-lowering-compose"]
def loweringBySimulation : Prop :=
  ∀ [N : FreshNames], Shrink.Lowering.FreshNames.Lawful N → Shrink.Lowering.CallerBound ∧
    ∃ D : Shrink.Lowering.Diagram, D.Simulates ∧ D.Total ∧
      ∀ (S : Solidity.Roadmap.SourceSpec) (I : Solidity.Roadmap.IntrinsicSpec)
        (B : Shrink.Lowering.Binding S I), D.Lifts B

end Solidity.Goals
