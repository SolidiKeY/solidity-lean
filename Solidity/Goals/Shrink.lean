import Solidity.Tools.Goal
import Solidity.Correctness.Lowering.Checker.Contract
import Solidity.Lowering.V07.Scalar
import Solidity.Semantics.RunFuel
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
  fragment (`PublicCompilerTotal.ProgOk []`), with initial/final matching,
  stuttering, progress, source determinacy, a backward diagram, fresh-state
  soundness and coverage of every fragment production run.

Session level, deferred by H556 (not hidden): the lift of this diagram to a
frozen `Roadmap.Lowering S I` and a `G49Final.PassCorrect` per program needs
the actual intrinsic session semantics (Event/Outcome prefixes over the
emitted programs), which does not exist at the base. Quantifying over every
`IntrinsicSpec` with a free target-session reference would make the goal
impossible, and an existential one would make it arbitrary, so this goal
states no session-level conjunct. Plan step is0-intrinsic-session defines that
semantics; sg1-restate-lowering-goal then adds the lift against it, with the
program-to-body binding (every resolved function body of the actual Source
program) and the resource transport tied to the diagram's fuel.

## Limitations (stated, not hidden)

* No function from the raw input to its resolved Source statement exists at
  the base. `Diagram.Total` therefore asks, for every fragment production
  run, for SOME resolved Source statement with the same production input
  (`Body.SameInput`: site, raw input, return slots, scope and state) that the
  diagram simulates; the source context, environment and statement are
  existential. The goal so says "every emitted fragment program is simulated
  by some Source statement", not "by the statement its raw input means": a
  lowering that miscompiles into another Source-expressible behaviour is not
  excluded here. Binding the raw input to its resolved statement is part of
  sg1-restate-lowering-goal, with the program-to-body binding.
* The diagram's value and global relations are its own invariant, bound only
  by Boolean/integer reflection and total initial matching; storage and event
  agreement is a session-level obligation (sg1).
* The goal is stated for the production fresh-name policy
  (`productionNames`), not for the per-file `FreshNames.ofTable` instances of
  chain examples.

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
  | slot (region : Region) (word : Roadmap.Word) (byte : Nat)
  | mem (address : Nat)

/-- A word of `2 ^ 256`, from a natural number. -/
def toWord (n : Nat) : Roadmap.Word := ⟨n % 2 ^ 256, Nat.mod_lt _ (by decide)⟩

/-- The byte a cell holds. -/
def Phys.byte (m : Phys) : Cell → Nat
  | .slot .storage w b => (m.storage w).val / 256 ^ b % 256
  | .slot .transient w b => (m.transient w).val / 256 ^ b % 256
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

/-- The footprint `[base, base + size)` of a memory object. -/
def objectCells (base size : Nat) : Cell → Prop
  | .mem x => base ≤ x ∧ x < base + size
  | .slot _ _ _ => False

mutual
/-- The static storage slots a layout occupies (solc's storage layout):
narrow scalars of an array pack `32 / w` per slot, struct members pack by
`packedStart` and an aggregate member starts a fresh slot; a dynamic array,
bytes or mapping takes its one head slot. -/
def Layout.slots : Layout → Nat
  | .scalar _ => 1
  | .fixedArray (.scalar w) n => (n + 32 / w - 1) / (32 / w)
  | .fixedArray e n => n * e.slots
  | .dynArray _ => 1
  | .bytes => 1
  | .struct fs => (Layout.memberEnd fs 0 + 31) / 32
  | .mapping _ => 1
/-- The byte cursor after struct members from `cursor`. -/
def Layout.memberEnd : List Layout → Nat → Nat
  | [], cursor => cursor
  | .scalar w :: fs, cursor => Layout.memberEnd fs (packedStart cursor w + w)
  | f :: fs, cursor => Layout.memberEnd fs ((cursor + 31) / 32 * 32 + 32 * f.slots)
end

/-- The byte start of struct member `i` from `cursor`. -/
def Layout.memberStart : List Layout → Nat → Nat → Nat
  | [], _, _ => 0
  | .scalar w :: _, cursor, 0 => packedStart cursor w
  | _ :: _, cursor, 0 => (cursor + 31) / 32 * 32
  | .scalar w :: fs, cursor, i + 1 => Layout.memberStart fs (packedStart cursor w + w) i
  | f :: fs, cursor, i + 1 => Layout.memberStart fs ((cursor + 31) / 32 * 32 + 32 * f.slots) i

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
regions. Later shapes are `Geometric`/`Instances` work (yv2/yv3). -/
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

/-! ## Lowering by simulation -/

namespace Lowering

open Solidity.Correctness.Lowering.Checker (Snapshot Input Output ElaborationReceipt)
open Solidity.Lowering.V07 (ContextMap IntValueRel integerPrim)

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
  /-- A recursive callee's frame body (Arms.lean:1063-1075): `calleeBody`, then
  `(elabStmtsP body).runFrom sc'` from `(Γf, k₁)` with an empty memo, `sc'` the
  callee scope over the scope `outer` read then, with the frame `rf` pushed. -/
  | recursive (d : FunDecl) (ρ : List (String × String)) (ctor selfFrame : Bool) (Γf : ECtx)
      (funs : List (Name × FunDecl)) (k₀ : Nat) (outer : ElabScope) (rf : RecFrame)

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
  | .callee d ρ ctor selfFrame Γf _ _ | .recursive d ρ ctor selfFrame Γf _ _ _ _ =>
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
  match b.site with
  | .loop => u.output.beforeElab.memo = u.output.afterLower.memo ∧
    u.output.elabScope = b.input.scope ∧ u.output.beforeElab.locals = u.output.afterLower.locals
  | .recursive _ _ _ selfFrame Γf funs k₀ outer rf =>
    u.output.beforeElab.memo = {} ∧
    u.output.beforeElab.locals = (Γf, u.output.afterLower.locals.2) ∧
    u.output.elabScope = { calleeScope outer funs selfFrame k₀ u.output.afterLower.locals.2 with
      recs := rf :: outer.recs }
  | .callee _ _ _ selfFrame Γf funs k₀ =>
    u.output.beforeElab.memo = u.output.afterLower.memo ∧
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
source matches nothing. A target `exhausted` (`storage.full`, `assumeFalse`,
payments: Run.lean, RunAccel.lean, PaymentWorld.lean) matches nothing either,
so the backward clause obliges the prover to show associated fragment
programs never reach one; it is not assumed. -/
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

/-- Two bodies with the same production input (site, raw input, slots,
scope and state); only their resolved source may differ. -/
def Body.SameInput (b' b : Body) : Prop :=
  b'.site = b.site ∧ b'.input.raw = b.input.raw ∧ b'.input.returnSlots = b.input.returnSlots ∧
    b'.input.scope = b.input.scope ∧ b'.input.before = b.input.before

/-- **Coverage of t0's fragment**: every actual production run whose emitted
program is in the fragment has a resolved source, at the same site and with
the same raw input, slots, scope and state, that the diagram associates with
it. See "Limitations" in the module docstring: the source is existential. -/
def Diagram.Total (D : Diagram) : Prop :=
  ∀ (b : Body) (u : Emitted), Production b u → Accepted u →
    ∃ b' : Body, b'.SameInput b ∧ ∃ m, D.Assoc b' u m

/-- The production fresh-name policy: the default instance (AST.lean,
`.ofPrefixes "se" "sp" "ie" "mv"`), which every file without its own uses. -/
def productionNames : FreshNames := .ofPrefixes "se" "sp" "ie" "mv"

end Lowering

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

/-- Production lowering on t0's fragment by one simulation diagram, under the
production fresh-name policy; its session-level lift to `Lowering`/`PassCorrect`
is added by sg1-restate-lowering-goal (H556). -/
@[goal Solidity.Correctness.Lowering.Sim.lowering_producer "ls3-lowering-compose"]
def loweringBySimulation : Prop :=
  letI : FreshNames := Shrink.Lowering.productionNames
  Shrink.Lowering.CallerBound ∧
    ∃ D : Shrink.Lowering.Diagram, D.Simulates ∧ D.Total

end Solidity.Goals
