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

| Shape | Declaration | Instance conjunct |
|---|---|---|
| packed storage/transient scalar | `scalarPathView` (ScalarWriteback.lean:95) | `Instances.scalar` |
| finite separated scalar paths | `finiteView`, `pathsApart` (FinitePaths.lean:17,30) | `Instances.finite`, `Instances.apart` |
| persistent + transient cells | `FiniteCellWrites.Views` (FiniteCellWrites.lean:26) | `Instances.cells` |
| fixed word array in memory | `wordListView` (AggregateMemoryWords.lean:8) | `Instances.wordList` |
| dynamic word array in memory | `dynamicUintView` (DynamicUintMemory.lean:12) | `Instances.dynamicUint` |
| fixed or dynamic member array | `memberArrayView` (MemberArray.lean:121) | `Instances.memberArray` |
| bytes/string object | `bytesObjectView` (ByteObjects.lean:13) | `Instances.bytesObject` |
| bytes allocation | `byteAllocationView` (HeapByteAllocation.lean:51) | `Instances.byteAllocation` |
| any heap object allocation | `objectAllocationView` (ObjectMemoryAllocation.lean:37) | `Instances.objectAllocation` |
| whole placed heap | `enumeratedMemoryView`, `Placement` (EnumeratedMemory.lean:16, MemoryContract.lean:48) | `Instances.enumerated` |
| typed heap write and its failure | `Source.heapPut` via `heapPutConcrete_run/_error` (JointMemory.lean:9-32) | `Laws.illTyped` |

Mappings and nested storage aggregates have no per-shape view definition at
the base (their statements go through `scalarPathView` at hashed slots,
`physicalSlot`); `Layout.mapping`/`Layout.struct` cover them through the same
scalar instance at the keyed/field locations.
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

/-- The pipeline/codec parameters every law quantifies over: the slot hash
(as `physicalSlot` reads it), whether dirty high bits are cleaned on read,
and the solc pipeline. -/
structure Params where
  hash : Storage.Pre → Nat
  cleanDirty : Bool
  pipeline : Roadmap.Pipeline

/-- The per-constructor geometry of the view. The view itself is NOT a field:
it is `Geometry.read`, one structural recursion over `Layout`. -/
structure Geometry where
  scalar : Params → Nat → Loc → Phys → Option Nat
  elem : Params → Layout → Loc → Nat → Loc
  field : Params → List Layout → Loc → Nat → Loc
  length : Params → Loc → Phys → Nat
  data : Params → Loc → Phys → Loc
  key : Params → Loc → Roadmap.Word → Loc
  blob : Params → Loc → Phys → Option (List UInt8)
  /-- The cells a scalar, a dynamic length word and a blob read. -/
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

mutual
/-- The trees a layout admits (the typing the laws preserve). -/
def Layout.Fits : Layout → Tree → Prop
  | .scalar w, .leaf v => v < 256 ^ w
  | .fixedArray e n, .node xs => xs.length = n ∧ Layout.FitsAll e xs
  | .dynArray e, .node xs => xs.length < 2 ^ 64 ∧ Layout.FitsAll e xs
  | .bytes, .blob bs => bs.length < 2 ^ 64
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

/-- The free-memory pointer (`mload(0x40)`). -/
def Phys.free (m : Phys) : Nat := mloadNat m.memory 64

/-- The view with its operations. `write` and `alloc` are the only physical
updates; their laws read the one recursive `read` and `cells`. -/
structure LayoutView where
  geometry : Geometry
  write : Params → Layout → Loc → Tree → Phys → Option Phys
  alloc : Params → Layout → Tree → Phys → Option (Nat × Phys)

/-- Distinct slot preimages land in distinct slots (the aliasing premise of a
read-after-write; it is a premise of the laws, never of an instance). -/
def Params.Separating (P : Params) : Prop :=
  ∀ a b, (physicalSlot P.hash a = physicalSlot P.hash b) → a = b

/-- The laws, proved once for every layout, location, value and parameters. -/
structure LayoutView.Laws (V : LayoutView) : Prop where
  /-- A read depends on its footprint only. -/
  local_read : ∀ P L l m m', (∀ c, V.geometry.cells P L l m c → m.byte c = m'.byte c) →
    V.geometry.read P L l m = V.geometry.read P L l m'
  /-- Read after write, at storage and transient locations, for every fitting value. -/
  write_read : ∀ P L l t m m', P.Separating → L.Fits t → V.write P L l t m = some m' →
    V.geometry.read P L l m' = some t
  /-- A fitting persistent/transient write succeeds. -/
  write_total : ∀ P L l t m, l.region ≠ .memory → L.Fits t → ∃ m', V.write P L l t m = some m'
  /-- An ill-typed write fails, never a no-op (as `heapPutConcrete_error`). -/
  illTyped : ∀ P L l t m, ¬ L.Fits t → V.write P L l t m = none
  /-- Frame: a write changes its own footprint only. -/
  frame : ∀ P L l t m m', V.write P L l t m = some m' →
    ∀ c, ¬ V.geometry.cells P L l m' c → ¬ V.geometry.cells P L l m c → m'.byte c = m.byte c
  /-- Allocation: the value is readable at the returned address, which is at
  or above the old free pointer, and the new free pointer is above the
  object's footprint; storage, transient and memory below the old free
  pointer are unchanged. -/
  alloc_read : ∀ P L t m a m', L.Fits t → V.alloc P L t m = some (a, m') →
    V.geometry.read P L ⟨.memory, a, 0⟩ m' = some t ∧ m.free ≤ a ∧
    (∀ x, V.geometry.cells P L ⟨.memory, a, 0⟩ m' (.mem x) → m.free ≤ x ∧ x < m'.free) ∧
    m'.storage = m.storage ∧ m'.transient = m.transient ∧
    (∀ x, x < m.free → x ≠ 64 → x ≥ 96 → m'.memory x = m.memory x)
  /-- A fitting allocation within the address space succeeds. -/
  alloc_total : ∀ P L t m, L.Fits t → m.free < 2 ^ 64 → ∃ a m', V.alloc P L t m = some (a, m')

/-- The slot view with memory and transient slots left as they are. -/
def Phys.withStorage (m : Phys) (s : SlotView) : Phys := { m with storage := s }

/-- The memory image with slots left as they are. -/
def Phys.withMemory (m : Phys) (b : ByteView) : Phys := { m with memory := b }

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

/-- **The instance relation**: each existing per-shape view definition is the
recursive view at a concrete layout, location and tree. -/
structure LayoutView.Instances (V : LayoutView) : Prop where
  /-- `scalarPathView`: a packed field of a persistent or transient slot. -/
  scalar : ∀ (P : Params) (f : Field) (slot : Roadmap.Word) (m : Phys),
    V.geometry.read P (.scalar f.width) ⟨.storage, slot.val, f.offset⟩ m =
      some (.leaf (f.findWord (m.storage slot)).val) ∧
    V.geometry.read P (.scalar f.width) ⟨.transient, slot.val, f.offset⟩ m =
      some (.leaf (f.findWord (m.transient slot)).val)
  /-- `scalarPathView` itself, at every path, codec and store. -/
  scalarPath : ∀ (P : Params) {D : Source.Layout} {L : Source.SPath → Source.STy} {f : Field}
    (p : Source.SPath) (c : ScalarCodec D (L p) f) (slot : Roadmap.Word)
    (s : Source.Storage D L) (m : Phys),
    scalarPathView p c slot s m.storage ↔
      (s.read p).map (fun v => Tree.leaf (c.encode v).val) =
        V.geometry.read P (.scalar f.width) ⟨.storage, slot.val, f.offset⟩ m
  /-- `pathsApart`: separation is footprint disjointness. -/
  apart : ∀ (P : Params) {D : Source.Layout} {L : Source.SPath → Source.STy}
    (c d : ScalarPath D L) (m : Phys),
    pathsApart c d ↔ ∀ x, ¬ (V.geometry.cells P (.scalar c.field.width)
        ⟨.storage, c.slot.val, c.field.offset⟩ m x ∧
      V.geometry.cells P (.scalar d.field.width) ⟨.storage, d.slot.val, d.field.offset⟩ m x)
  /-- `finiteView`: the conjunction of scalar instances. -/
  finite : ∀ (P : Params) {D : Source.Layout} {L : Source.SPath → Source.STy}
    (cs : List (ScalarPath D L)) (s : Source.Storage D L) (m : Phys),
    finiteView cs s m.storage ↔ ∀ c ∈ cs,
      (s.read c.path).map (fun v => Tree.leaf (c.codec.encode v).val) =
        V.geometry.read P (.scalar c.field.width) ⟨.storage, c.slot.val, c.field.offset⟩ m
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
  /-- `dynamicUintView`: a dynamic array of words (length word, then words). -/
  dynamicUint : ∀ (P : Params) (n : Nat) (bound : n < 2 ^ 256) (words : Fin n → Roadmap.Word)
    (r : ByteView) (base : Nat) (m : Phys),
    V.geometry.read P (.dynArray (.scalar 32)) ⟨.memory, base, 0⟩
        (m.withMemory (dynamicUintView n bound words r base)) =
      some (.node ((List.ofFn words).map fun w => .leaf w.val)) ∧
    ∀ x, V.geometry.cells P (.dynArray (.scalar 32)) ⟨.memory, base, 0⟩
        (m.withMemory (dynamicUintView n bound words r base)) x ↔
      objectCells base ((MemoryShape.array true n).size) x
  /-- `memberArrayView`: dynamic when unsized, fixed otherwise. -/
  memberArray : ∀ (P : Params) (k : Option Nat) (n : Nat) (bound : n < 2 ^ 256)
    (words : Fin n → Roadmap.Word) (r : ByteView) (base : Nat) (m : Phys),
    V.geometry.read P (memoryShapeLayout (.array k.isNone n)) ⟨.memory, base, 0⟩
        (m.withMemory (memberArrayView k n bound words r base)) =
      some (.node ((List.ofFn words).map fun w => .leaf w.val))
  /-- `bytesObjectView`: a bytes/string object (length word, then bytes). -/
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
  allocation of its shape's layout, at the same base and image. -/
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
    (∀ a b, (h.cells a).isSome → (h.cells b).isSome → a ≠ b → ∀ x,
      ¬ (V.geometry.cells P (memoryShapeLayout (p.shape a)) ⟨.memory, p.address a, 0⟩
          (m.withMemory image) x ∧
        V.geometry.cells P (memoryShapeLayout (p.shape b)) ⟨.memory, p.address b, 0⟩
          (m.withMemory image) x))


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

/-- The actual lowering ran on the input, from its scope and full state, to
the output's raw statements and state. -/
def Lowered {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (input : Input E R M k srcΓ) (output : Output C Γ) : Prop :=
  (((lowerAt input.returnSlots input.raw).run input.scope).run input.before.locals).run
    input.before.memo = .ok ((output.raw, output.afterLower.locals), output.afterLower.memo)

/-- The elaboration continues from the lowering's fresh counter and memo; a
standalone loop (no return slots) is elaborated at once, in the same scope. -/
def Threaded {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (input : Input E R M k srcΓ) (output : Output C Γ) : Prop :=
  output.beforeElab.locals.2 = output.afterLower.locals.2 ∧
  output.beforeElab.memo = output.afterLower.memo ∧
  (input.returnSlots = none → output.elabScope = input.scope ∧
    output.beforeElab.locals = output.afterLower.locals)

/-- **Production association**: actual lowering, actual elaboration
(`elabStmtsP`, `SProg.chain`), state threaded between them. -/
def Production {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (input : Input E R M k srcΓ) (output : Output C Γ) : Prop :=
  Lowered input output ∧ ElaborationReceipt output ∧ Threaded input output

/-- Freshness of the lowering (a conclusion, never a premise): the scope's
locals and the memo are untouched and the fresh counter only grows. -/
def LowerFresh {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (input : Input E R M k srcΓ) (output : Output C Γ) : Prop :=
  output.afterLower.locals.1 = input.before.locals.1 ∧ output.afterLower.memo = input.before.memo ∧
    input.before.locals.2 ≤ output.afterLower.locals.2

/-- t0's accepted fragment (`Goals/Total.lean`), read on the emitted program. -/
def Accepted {C : Contract} {Γ : Ctx} (output : Output C Γ) : Prop :=
  Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] output.program.2

/-- The actual Source run of the resolved statement at horizon `n`. -/
def sourceRun {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n nps : Nat) (ph : Option (Source.Ph E))
    (input : Input E R M k srcΓ) (s : Source.EMState E srcΓ) :=
  (Source.execS G F n nps ph input.resolved s.1).run (.nil, s.2)

/-- Halts correspond: a revert keeps its data (a panic's code is the
target's `panic`); a stuck or timed-out source matches nothing. -/
def HaltMatch : Source.Halt → THalt → Prop
  | .revert d, h => h = THalt.ofData d ∨ (h = .panic ∧ ∃ c, d = Source.panicData c)
  | .stuck _, _ => False
  | .timeout, _ => False

/-- A source body with its production input. -/
structure Body where
  E : Source.Env
  returns : List Source.STy
  modifier : Bool
  control : Source.SCtx
  ctx : Source.RCtx
  input : Input E returns modifier control ctx

/-- An emitted program with its production state. -/
structure Emitted where
  C : Contract
  Γ : Ctx
  output : Output C Γ

/-- **The one simulation**: its horizon transport, its association of a
resolved source with an actual production run, and its invariant (value and
global relations). -/
structure Diagram where
  fuel : Nat → Nat
  Assoc : {E : Source.Env} → {R : List Source.STy} → {M : Bool} → {k : Source.SCtx} →
    {srcΓ : Source.RCtx} → {C : Contract} → {Γ : Ctx} →
    Input E R M k srcΓ → Output C Γ → ContextMap srcΓ Γ → Prop
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

* the value relation reflects Booleans and integers (`IntValueRel`), so the
  invariant cannot be degenerate on observable scalars;
* initial matching (related locals and globals) gives, at every source
  horizon that completes, the matching final target result at the
  transported fuel (forward diagram; a source timeout is stuttering);
* the transport is monotone (progress) and completed source runs are stable
  under larger horizons (Source determinacy, needed for `back`);
* every completed target run is matched by some completed source run
  (backward diagram: nondeterminism is not dropped, determinacy is proved);
* the lowering's fresh state is sound (`LowerFresh`). -/
def Diagram.Simulates (D : Diagram) : Prop :=
  (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (v : Source.Val Dl .bool) (b : Bool),
    D.valRel (C := C) (H := H) .bool (.val .bool) v b → v = .bool b) ∧
  (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (t : Source.IntTy) (v : Source.Val Dl (.int t))
    (x : (integerPrim t).Denote), D.valRel (C := C) (H := H) (.int t) (.val (integerPrim t)) v x →
      IntValueRel t v x) ∧
  (∀ n n', n ≤ n' → D.fuel n ≤ D.fuel n') ∧
  ∀ {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} (input : Input E R M k srcΓ) (output : Output C Γ)
    (m : ContextMap srcΓ Γ), Production input output → Accepted output → D.Assoc input output m →
    LowerFresh input output ∧
    ∃ emb : Thin Γ output.program.1,
    ∀ (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
      (src : Source.EMState E srcΓ) (tgt : State C Γ),
      m.Related (fun τ u => D.valRel τ u) src.1 tgt.env → D.globRel src.2 tgt →
      (∀ n, (sourceRun G F n nps ph input src).1 ≠ .error .timeout →
        D.Final m emb (sourceRun G F n nps ph input src)
          (output.program.2.runF (D.fuel n) tgt)) ∧
      (∀ n n', n ≤ n' → (sourceRun G F n nps ph input src).1 ≠ .error .timeout →
        sourceRun G F n' nps ph input src = sourceRun G F n nps ph input src) ∧
      (∀ n, output.program.2.runF n tgt ≠ .error .diverge →
        ∃ j, D.Final m emb (sourceRun G F j nps ph input src) (output.program.2.runF n tgt))

/-- **Coverage of t0's fragment**: every actual production run whose emitted
program is in the fragment has a resolved source, with the same raw input,
slots, scope and state, that the diagram associates with it. -/
def Diagram.Total (D : Diagram) : Prop :=
  ∀ (b : Body) (u : Emitted), Production b.input u.output → Accepted u.output →
    ∃ b' : Body, b'.input.raw = b.input.raw ∧ b'.input.returnSlots = b.input.returnSlots ∧
      b'.input.scope = b.input.scope ∧ b'.input.before = b.input.before ∧
      ∃ m, D.Assoc b'.input u.output m

/-- The binding of a source/intrinsic pair to the actual programs: a
resolution's Source program (the frozen P8a origins) whose failure-free
prefixes are actual `Source.sessionAt` sessions, its production bodies
(the resolved-source association), the profile inside t0's fragment, and the
emitted programs of a world, whose sessions the world's semantics reads. -/
structure Binding (S : SourceSpec) (I : IntrinsicSpec) where
  origins : Solidity.Lowering.P8.P8a.SourceOrigins S
  program : S.lang.Prog → Solidity.Lowering.P8.P8a.SourceProgram
  program_meaning : ∀ r w p art, program (S.meaning r w p art) = origins.meaning r w p art
  horizon : S.lang.Res → Nat
  source_exact : ∀ prog e res, S.NoFailure res →
    S.lang.sem prog e res = Source.sessionAt (program prog).2 (S.session e) (horizon res)
  bodies : S.Resolved → List Body
  bodies_env : ∀ r w p art, ∀ b ∈ bodies r, b.E = (origins.meaning r w p art).1
  fragment : ∀ r, S.WellFormed r → S.InProfile r → ∀ b ∈ bodies r, ∀ u : Emitted,
    Production b.input u.output → Accepted u.output
  units : I.World → List Emitted
  targetHorizon : I.lang.Res → Nat
  targetSession : List Emitted → SessionEnv → I.lang.Res → Prefix Event Outcome
  target_exact : ∀ w e res,
    I.lang.sem (I.ofWorld w) e res = targetSession (units w) (I.session e) res

/-- **Both carriers from the same diagram**: a frozen `Lowering S I` whose
worlds are exactly the production outputs of the resolution's bodies, each
associated by the diagram, whose environment map is the exact session
environment and whose resource transport is the diagram's fuel; and, for
every program, a `PassCorrect` between the actual behaviours with the SAME
environment map and resource transport (all `Cert`/`PassCorrect` fields,
forward and back, are retained by their types). -/
def Diagram.Lifts (D : Diagram) {S : SourceSpec} {I : IntrinsicSpec} (B : Binding S I) : Prop :=
  ∃ L : Solidity.Roadmap.Lowering S I,
    (∀ e, L.pass.envAbs e = S.ofSession (I.session e)) ∧
    (∀ r w p art, (B.units (L.lower r w p art)).length = (B.bodies r).length ∧
      ∀ bu ∈ (B.bodies r).zip (B.units (L.lower r w p art)),
        Production bu.1.input bu.2.output ∧ ∃ m, D.Assoc bu.1.input bu.2.output m) ∧
    (∀ r w p art e res, B.targetHorizon (L.cert.need (S.meaning r w p art) (L.dom r w p art) e res) =
      D.fuel (B.horizon res)) ∧
    ∃ pc : (r : S.Resolved) → (w : S.WellFormed r) → (p : S.InProfile r) → (art : Artifact) →
        Solidity.Roadmap.G49Final.PassCorrect
          (Solidity.Roadmap.G49Final.Behaviour.ofLang S.lang (S.meaning r w p art))
          (Solidity.Roadmap.G49Final.Behaviour.ofLang I.lang (I.ofWorld (L.lower r w p art))),
      ∀ r w p art, (pc r w p art).envAbs = L.pass.envAbs ∧
        (pc r w p art).need = L.cert.need (S.meaning r w p art) (L.dom r w p art)

end Lowering

end Solidity.Goals.Shrink

namespace Solidity.Goals

open Solidity.Goal

/-- One recursive layout-indexed view with its laws and every per-shape instance. -/
@[goal Solidity.Yul.Layout.view_correct "yv1-yul-layout-view"]
def yulLayoutView : Prop :=
  ∃ V : Shrink.LayoutView, V.Laws ∧ V.Instances

/-- Production lowering on t0's fragment by one simulation, lifted to a frozen
`Lowering` and a direct `PassCorrect` from the same diagram. -/
@[goal Solidity.Correctness.Lowering.Sim.lowering_producer "ls3-lowering-compose"]
def loweringBySimulation : Prop :=
  ∀ [FreshNames], Shrink.Lowering.CallerBound ∧
    ∃ D : Shrink.Lowering.Diagram, D.Simulates ∧ D.Total ∧
      ∀ (S : Solidity.Roadmap.SourceSpec) (I : Solidity.Roadmap.IntrinsicSpec)
        (B : Shrink.Lowering.Binding S I), D.Lifts B

end Solidity.Goals
