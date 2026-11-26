import Solidity.Yul.Layout.Shared.Vocabulary

/-! Recursive layout operations and their general laws. Public declarations
retain their original `Solidity.Goals.Shrink` namespace. -/
namespace Solidity.Goals.Shrink

open Solidity.Yul.Views

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

end Solidity.Goals.Shrink
