import Solidity.Goals.Shrink

/-!
# The geometry of the one layout view

`geometry` fills the 13 leaf fields of `Shrink.Geometry`. The fields that
`Shrink.LayoutView.Geometric` pins are transcribed from its right-hand sides
(`Solidity.Yul.Layout.geometric` checks the transcription). The rest is chosen
so that the `LayoutView.Laws` can hold:

* A slot scalar whose field does not fit its slot (`offset + width > 32`) is
  read and written at offset 0 (`slotField`): a fitting persistent write must
  succeed at every location (`write_total`) and read back (`write_read`).
* Storage and transient `bytes`: the head slot holds the length (as a dynamic
  array's does), byte `i` is byte `31 - i % 32` of slot `keccak(slot) + i / 32`.
  The data footprint is every slot the data of a fitting length can reach
  (`2 ^ 251` slots from `keccak(slot)`), not only the slots of the current
  length: `Geometry.cellsT` takes a `bytes` footprint from the result state,
  where a later sibling write may have overwritten the head slot, so a
  footprint that depends on the stored length would miss cells the write
  changed (`frame`). solc's short/long encoding (`2 * length + 1`) is not used: it cannot store a
  length of `2 ^ 255` or more, which `Layout.Fits` admits.
* Memory objects are inline: element `i` starts `i * memSize e` after the
  base. `Geometry.elem` and `Geometry.scalarCells` see no state, so a nested
  dynamic array or `bytes` cannot be reached through an ordinary pointer word.
  A nested dynamic member is a two-word header (length, data address) at a
  location with a nonzero `offset` (`indirect`); `dataLoc` follows the address
  and the length footprint covers both words. A dynamic array or `bytes` at
  offset 0 is the pinned object (`bytesObjectView`, `memberArrayView`): length
  word, then data.
* A length or `bytes` write through an indirect header is refused: an element
  write could overwrite the data address, and then the written footprint
  (taken in the result state) would miss the cells changed (`frame`). Such
  objects are built by the allocator.

No allocator and no `LayoutView` are defined here.
-/
namespace Solidity.Yul.Layout

open Solidity.Goals
open Solidity.Yul.Views

/-- The packed field a slot scalar of `width` bytes at byte `offset` uses: the
field itself when it fits the slot, the low bytes of the slot otherwise, none
for a width outside 1–32. -/
def slotField (width offset : Nat) : Option Field :=
  if h : 0 < width ∧ offset + width ≤ 32 then some ⟨offset, width, h.1, h.2⟩
  else if h : 0 < width ∧ width ≤ 32 then some ⟨0, width, h.1, by omega⟩
  else none

mutual
/-- The bytes a nested value occupies inline in memory: a word per scalar, a
two-word header (length, data address) per dynamic array or `bytes`, a word
for a mapping (which no memory object holds). -/
def memSize : Shrink.Layout → Nat
  | .scalar _ => 32
  | .fixedArray e n => n * memSize e
  | .dynArray _ => 64
  | .bytes => 64
  | .struct fs => memSizes fs
  | .mapping _ => 32
/-- The inline memory bytes of a member list. -/
def memSizes : List Shrink.Layout → Nat
  | [] => 0
  | f :: fs => memSize f + memSizes fs
end

/-- The inline memory byte offset of member `i`. -/
def memberOffset : List Shrink.Layout → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | f :: fs, i + 1 => memSize f + memberOffset fs i

/-- The `offset` of the memory location of a nested value: 1 for a dynamic
array or `bytes` (a header with a data address), 0 otherwise. -/
def indirect : Shrink.Layout → Nat
  | .dynArray _ | .bytes => 1
  | _ => 0

/-- Where dynamic data starts: `keccak(slot)` in storage; in memory after the
length word, or at the address the second header word holds when indirect. -/
def dataLoc (P : Shrink.Params) (l : Shrink.Loc) (m : Shrink.Phys) : Shrink.Loc :=
  if l.region = .memory then
    ⟨.memory, if l.offset = 0 then l.word + 32 else mloadNat m.memory (l.word + 32), 0⟩
  else ⟨l.region, (physicalSlot P.hash (.data (.root l.word) 0)).val, 0⟩

/-- `count` bytes of slot data from slot `base`: byte `i` is byte
`31 - i % 32` (counted from the least significant) of slot `base + i / 32`. -/
def readSlotBytes (s : SlotView) (base count : Nat) : List UInt8 :=
  (List.range count).map fun i =>
    UInt8.ofNat ((s (Shrink.toWord (base + i / 32))).val / 256 ^ (31 - i % 32))

/-- Bytes `i, i + 1, …` of slot data patched in, one one-byte field each. -/
def writeSlotBytes (base : Nat) : List UInt8 → Nat → SlotView → SlotView
  | [], _, s => s
  | b :: bs, i, s =>
    writeSlotBytes base bs (i + 1)
      (patchScalarSlot s (Shrink.toWord (base + i / 32)) ⟨31 - i % 32, 1, by decide, by omega⟩
        ⟨b.toNat, b.toNat_lt⟩)

/-- **The geometry** of the layout view. -/
def geometry : Shrink.Geometry where
  scalar P w l m :=
    if l.region = .memory then
      some (if P.cleanDirty then mloadNat m.memory l.word % 256 ^ w else mloadNat m.memory l.word)
    else (slotField w l.offset).map fun f => (f.findWord (m.slots l.region (Shrink.toWord l.word))).val
  writeScalar _ w l v m :=
    if l.region = .memory then some (m.withMemory (mstore m.memory l.word (Shrink.toWord v)))
    else (slotField w l.offset).bind fun f =>
      if h : v < f.modulus then
        some (m.withSlots l.region
          (patchScalarSlot (m.slots l.region) (Shrink.toWord l.word) f ⟨v, h⟩))
      else none
  elem _ e l i :=
    if l.region = .memory then ⟨.memory, l.word + memSize e * i, indirect e⟩
    else match e with
      | .scalar w => ⟨l.region, (Shrink.toWord (l.word + i / (32 / w))).val, i % (32 / w) * w⟩
      | e => ⟨l.region, (Shrink.toWord (l.word + i * e.slots)).val, 0⟩
  field _ fs l i :=
    if l.region = .memory then
      ⟨.memory, l.word + memberOffset fs i, (fs[i]?.map indirect).getD 0⟩
    else ⟨l.region, (Shrink.toWord (l.word + Shrink.Layout.memberStart fs 0 i / 32)).val,
      Shrink.Layout.memberStart fs 0 i % 32⟩
  length _ l m :=
    if l.region = .memory then mloadNat m.memory l.word
    else (m.slots l.region (Shrink.toWord l.word)).val
  writeLength _ l n m :=
    if l.region = .memory then
      if l.offset = 0 then some (m.withMemory (mstore m.memory l.word (Shrink.toWord n))) else none
    else some (m.withSlots l.region
      (saveSlot (m.slots l.region) (Shrink.toWord l.word) (Shrink.toWord n)))
  data := dataLoc
  key P l k := ⟨l.region, (physicalSlot P.hash (.hash k.val (.root l.word) 0)).val, 0⟩
  blob P l m :=
    if l.region = .memory then
      some (readBytes m.memory (dataLoc P l m).word (mloadNat m.memory l.word))
    else some (readSlotBytes (m.slots l.region) (dataLoc P l m).word
      (m.slots l.region (Shrink.toWord l.word)).val)
  writeBlob P l bs m :=
    if h : bs.length < 2 ^ 256 then
      if l.region = .memory then
        if l.offset = 0 then some (m.withMemory (bytesObjectView bs h m.memory l.word)) else none
      else some (m.withSlots l.region
        (saveSlot (writeSlotBytes (dataLoc P l m).word bs 0 (m.slots l.region))
          (Shrink.toWord l.word) ⟨bs.length, h⟩))
    else none
  scalarCells _ w l c :=
    if l.region = .memory then Shrink.objectCells l.word 32 c
    else match slotField w l.offset with
      | some f => ∃ b, c = .slot l.region (Shrink.toWord l.word) b ∧ f.offset ≤ b ∧ b < f.offset + f.width
      | none => False
  lengthCells _ l c :=
    if l.region = .memory then Shrink.objectCells l.word (if l.offset = 0 then 32 else 64) c
    else ∃ b, c = .slot l.region (Shrink.toWord l.word) b ∧ b < 32
  blobCells P l m c :=
    if l.region = .memory then
      Shrink.objectCells (dataLoc P l m).word (mloadNat m.memory l.word) c
    else ∃ j b, j < 2 ^ 251 ∧ b < 32 ∧
      c = .slot l.region (Shrink.toWord ((dataLoc P l m).word + j)) b

end Solidity.Yul.Layout
