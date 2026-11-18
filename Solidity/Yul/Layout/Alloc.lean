import Solidity.Yul.Layout.Geometry

/-!
# The allocator of the one layout view

`alloc` is bump allocation at the free pointer `Shrink.Phys.free`: the
free-pointer word is advanced by `allocSize`, then the tree is written at the
old free pointer, which is the returned address. It refuses a free pointer
inside the reserved words (`< 128`) and an object that does not end below
`2 ^ 256`.

The root object is the pinned one: a root `bytes` is `geometry.write`
(`bytesObjectView` over the memory with the advanced free pointer, the image
of `byteAllocationView`), a root dynamic array is its length word and then its
elements, anything else is its inline members (`put`). On a layout without a
nested dynamic array or `bytes` the writes are the `mstore`s of
`geometry.write`, in the sizes of `MemoryShape.size`; that they are the images
of `objectAllocationView` is left to `LayoutView.Instances.objectAllocation`.

A nested dynamic array or `bytes` cannot be written by `geometry.write`
(`Geometry.lean`: a write through an indirect header is refused), so `put`
builds it: the two-word header (length, data address) inline, the data out of
line at the tail pointer `f`. `tailSize` is the out-of-line size, so the tail
pointer of a later sibling is known without threading it through the result.
`put` always writes a dynamic array or `bytes` as an indirect header, whatever
the offset of the location: the root object goes through `allocAt`.
-/
namespace Solidity.Yul.Layout

open Solidity.Goals
open Solidity.Yul.Views

mutual
/-- The out-of-line bytes of a value: the elements of a dynamic array, the
payload of a `bytes` rounded up to words (so an aligned free pointer stays
aligned), and the same for everything nested below. -/
def tailSize : Shrink.Layout → Shrink.Tree → Nat
  | .fixedArray e _, .node xs => tailSizes e xs
  | .dynArray e, .node xs => xs.length * memSize e + tailSizes e xs
  | .bytes, .blob bs => (bs.length + 31) / 32 * 32
  | .struct fs, .node xs => tailFields fs xs
  | _, _ => 0
/-- The out-of-line bytes of a sequence of elements. -/
def tailSizes (e : Shrink.Layout) : List Shrink.Tree → Nat
  | [] => 0
  | x :: xs => tailSize e x + tailSizes e xs
/-- The out-of-line bytes of a member list. -/
def tailFields : List Shrink.Layout → List Shrink.Tree → Nat
  | g :: fs, x :: xs => tailSize g x + tailFields fs xs
  | _, _ => 0
end

mutual
/-- A nested value written inline at a memory location, its out-of-line data
from the tail pointer `f`. A dynamic array or `bytes` is an indirect header:
the length word, the data address `f`, and the data at `f`. -/
def put (P : Shrink.Params) :
    Shrink.Layout → Shrink.Loc → Shrink.Tree → Nat → Shrink.Phys → Option Shrink.Phys
  | .scalar w, l, .leaf v, _, m => geometry.write P (.scalar w) l (.leaf v) m
  | .fixedArray e n, l, .node xs, f, m =>
    if xs.length = n ∧ n < 2 ^ 256 then putElems P e l xs 0 f m else none
  | .dynArray e, l, .node xs, f, m =>
    if xs.length < 2 ^ 256 then
      putElems P e ⟨.memory, f, 0⟩ xs 0 (f + xs.length * memSize e)
        (m.withMemory (mstore (mstore m.memory l.word (Shrink.toWord xs.length)) (l.word + 32)
          (Shrink.toWord f)))
    else none
  | .bytes, l, .blob bs, f, m =>
    if bs.length < 2 ^ 256 then
      some (m.withMemory (copyBytes
        (mstore (mstore m.memory l.word (Shrink.toWord bs.length)) (l.word + 32) (Shrink.toWord f))
        (calldataBytes bs) f 0 bs.length))
    else none
  | .struct fs, l, .node xs, f, m => putFields P fs l fs xs 0 f m
  | _, _, _, _, _ => none
/-- Elements `i, i + 1, …` written at their `geometry.elem` locations. -/
def putElems (P : Shrink.Params) (e : Shrink.Layout) (l : Shrink.Loc) :
    List Shrink.Tree → Nat → Nat → Shrink.Phys → Option Shrink.Phys
  | [], _, _, m => some m
  | x :: xs, i, f, m =>
    (put P e (geometry.elem P e l i) x f m).bind
      (putElems P e l xs (i + 1) (f + tailSize e x))
/-- Members `i, …` of the struct `all` written at their `geometry.field` locations. -/
def putFields (P : Shrink.Params) (all : List Shrink.Layout) (l : Shrink.Loc) :
    List Shrink.Layout → List Shrink.Tree → Nat → Nat → Shrink.Phys → Option Shrink.Phys
  | [], [], _, _, m => some m
  | g :: fs, x :: xs, i, f, m =>
    (put P g (geometry.field P all l i) x f m).bind
      (putFields P all l fs xs (i + 1) (f + tailSize g x))
  | _, _, _, _, _ => none
end

/-- The bytes an allocation takes: a root `bytes` is its length word and its
payload rounded up to words (`MemoryShape.size`), a root dynamic array its
length word, elements and their out-of-line data, anything else its inline
members and their out-of-line data. -/
def allocSize (L : Shrink.Layout) (t : Shrink.Tree) : Nat :=
  match L with
  | .bytes | .dynArray _ => 32 + tailSize L t
  | _ => memSize L + tailSize L t

/-- The root object written at address `a`. -/
def allocAt (P : Shrink.Params) (L : Shrink.Layout) (a : Nat) (t : Shrink.Tree)
    (m : Shrink.Phys) : Option Shrink.Phys :=
  match L with
  | .bytes => geometry.write P .bytes ⟨.memory, a, 0⟩ t m
  | .dynArray e =>
    match t with
    | .node xs =>
      if xs.length < 2 ^ 256 then
        putElems P e ⟨.memory, a + 32, 0⟩ xs 0 (a + 32 + xs.length * memSize e)
          (m.withMemory (mstore m.memory a (Shrink.toWord xs.length)))
      else none
    | _ => none
  | _ => put P L ⟨.memory, a, 0⟩ t (a + memSize L) m

/-- **The allocator**: the free-pointer word advanced by `allocSize`, then the
tree written at the old free pointer, which is the address returned. -/
def alloc (P : Shrink.Params) (L : Shrink.Layout) (t : Shrink.Tree) (m : Shrink.Phys) :
    Option (Nat × Shrink.Phys) :=
  if 128 ≤ m.free ∧ m.free + allocSize L t < 2 ^ 256 then
    (allocAt P L m.free t
      (m.withMemory (mstore m.memory 64 (Shrink.toWord (m.free + allocSize L t))))).map
      fun m' => (m.free, m')
  else none

end Solidity.Yul.Layout
