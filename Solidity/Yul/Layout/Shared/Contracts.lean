import Solidity.Yul.Layout.Shared.Recursive
import Solidity.Yul.Views.ScalarWriteback
import Solidity.Yul.Views.MemoryContract

/-! Shared layout geometry and scalar correspondence contracts. The full
per-shape instance relation remains in `Solidity.Goals.Shrink`. -/
namespace Solidity.Goals.Shrink

open Solidity.Yul.Views

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
