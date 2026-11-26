import Solidity.Yul.Views.StorageContract
import Solidity.Yul.Views.WordMemory
import Solidity.Yul.Views.PackedAggregates

/-! Shared layout vocabulary and slot placement, independent of the per-shape
instance relation. The original `Solidity.Goals.Shrink` names are retained so
existing goals and consumers use the same definitions. -/
namespace Solidity.Goals.Shrink

open Solidity.Yul.Views

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

end Solidity.Goals.Shrink
