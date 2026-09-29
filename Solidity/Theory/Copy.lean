import Solidity.Theory.Storage

/-!
# The copying write and the array writes

`save` (`Theory/Storage.lean`) collapses its leaf: the value written is the
value read back.  That is the word write and `delAt`'s write.  A struct or an
array written over a location is solkey's non-collapsing `save`, the new value
laid over the old one — `copyTo`, which is `save` with a `copyAt` leaf
(`Theory/Terms.lean`, "Kinded nodes and the two lazy leaves").  The
`selectOnSaveEmpty{Map,Ref,Fixed,IndexStruct,Default}` are its laws:
`save(st, nil, v)` is `copyTo s [] v`, which is `copyAt s n` (`copyTo_nil`),
and each rule reads one member of it by the two kinds.

The array writes are here too, as the terms the calculus's `push`/`pop`
updates denote: `pushT` stores the element and then the length, `popT`
deletes the last element and then shrinks the length.  `fillSlot` is the
element a bare `push()` lands on (`Semantics.pushSlot`); it takes the default
as a value, so this module never needs the interpreter's `SVal.abs`.

The laws that are literal are here; the ones that hold only up to
`StValue.Equiv` (a copy, a delete, a pop, under a context) are
`Theory/Observe.lean`'s.
-/

namespace Solidity
namespace Theory

open Semantics

/-- Whether `new`'s kind is laid over `old`'s member by member — a mapping over a
mapping, an array over an array, a struct (or nothing) over a struct (or
nothing).  Where it is not, the copy lands on fresh slots (`selectOnCopyOther`). -/
def NodeKind.sameShape (ko kn : Option NodeKind) : Bool :=
  match kn with
  | some .map => ko == some .map
  | some (.arr _) => NodeKind.isArr ko
  | some .struct | none => NodeKind.isStructLike ko

namespace StValue

open Struct

/-! ## The operations -/

/-- solkey's `save(st, p, v)`: a word is stored, anything else is copied over what is there. -/
def copyTo (s : Struct) (p : List Seg) (v : StValue) : Struct := save s p (copyVal (findSt s p) v)

/-- `v` laid on fresh slots (`SVal.strip`). -/
def stripVal (v : StValue) : StValue := copyVal (st .mtSt) v

/-- The length of the array at `p`. -/
def lenAt (s : Struct) (p : List Seg) : Int := asInt (findSt s (p ++ [lengthSeg]))

/-- `push(w)` on the array at `p`: the element at the old length, then the length. -/
def pushT (s : Struct) (p : List Seg) (w : StValue) : Struct :=
  save (save s (p ++ [.at (lenAt s p)]) w) (p ++ [lengthSeg]) (int (lenAt s p + 1))

/-- The slot a bare `push()` lands on (`Semantics.pushSlot`): the default at a primitive
element type or where no slot ever was (kind `none`), otherwise the recycled slot as it is. -/
def fillSlot (isPrim : Bool) (dflt v : StValue) : StValue :=
  if isPrim then dflt else match v with
    | .st s => if s.kind = none then dflt else v
    | .prim _ => v

/-- A bare `push()` on the array at `p`. -/
def pushSlotT (isPrim : Bool) (dflt : StValue) (s : Struct) (p : List Seg) : Struct :=
  pushT s p (fillSlot isPrim dflt (findSt s (p ++ [.at (lenAt s p)])))

/-- `pop()` on the array at `p`: the last element deleted, then the length shrunk. -/
def popT (s : Struct) (p : List Seg) : Struct :=
  save (delAt s (p ++ [.at (lenAt s p - 1)])) (p ++ [lengthSeg]) (int (lenAt s p - 1))

/-- The length alone shrunk by one. -/
def shrinkT (s : Struct) (p : List Seg) : Struct :=
  save s (p ++ [lengthSeg]) (int (lenAt s p - 1))

/-! ## `copyTo` along a path -/

/-- One member of a copy: `copyRead`, the `copyAt` arm of `selectSt`. -/
theorem selectOnCopyAt (o n : Struct) (a : Seg) :
    selectSt (.copyAt o n) a =
      copyRead o.kind n.kind (lenOf o) (lenOf n) a (selectSt o a) (selectSt n a) := rfl

/-- `save(st, nil, v)`, the whole-node write: the `copyAt` leaf. -/
theorem copyTo_nil (s n : Struct) : copyTo s [] (st n) = .copyAt s n := rfl

/-- A word is stored as it is. -/
theorem copyTo_prim (s : Struct) (p : List Seg) (x : PrimVal) :
    copyTo s p (.prim x) = save s p (.prim x) := rfl

/-- Reading exactly the copied path: the new value over the old one. -/
theorem find_copyTo_same (s : Struct) {p : List Seg} (hp : p ≠ []) (v : StValue) :
    findSt (copyTo s p v) p = copyVal (findSt s p) v :=
  find_save_same s hp _

/-- A read off the copied path does not see the copy. -/
theorem find_copyTo_frame (s : Struct) (v : StValue) (p q : List Seg) (h : diverges p q = true) :
    findSt (copyTo s p v) q = findSt s q :=
  find_save_frame s _ p q h

/-- A read below the copied path reads out of the copy. -/
theorem find_copyTo_extends (s : Struct) {p q : List Seg} (hp : p ≠ []) (hq : q ≠ [])
    (v : StValue) :
    findSt (copyTo s p v) (p ++ q) = findSt (asStruct (copyVal (findSt s p) v)) q :=
  find_save_extends s hp hq _

/-! ## A member of a whole-node copy, by the member's sort

The rules `selectOnSaveEmpty*`, each one selector down from
`save(st, nil, v)` = `copyTo s [] (st n)`, the member's sort a premise on the
two kinds. -/

/-- A struct-like kind is a struct or nothing. -/
private theorem structLike_cases :
    ∀ {k : Option NodeKind}, NodeKind.isStructLike k = true -> k = none ∨ k = some .struct
  | none, _ => .inl rfl
  | some .struct, _ => .inr rfl
  | some .map, h => absurd h (by decide)
  | some (.arr fx), h => by cases fx <;> exact absurd h (by decide)

/-- **`selectOnSaveEmptyRef`** (and **`selectOnSaveEmptyFixed`**) — a member of a
struct copied over a struct is the member copied over the member. -/
theorem selectOnCopyRef {s n : Struct} {a : Seg}
    (hs : NodeKind.isStructLike s.kind = true) (hn : NodeKind.isStructLike n.kind = true) :
    asStruct (selectSt (copyTo s [] (st n)) a) =
      copyTo (asStruct (selectSt s a)) [] (selectSt n a) := by
  show asStruct (copyRead s.kind n.kind _ _ a (selectSt s a) (selectSt n a)) = _
  rcases structLike_cases hn with hk | hk <;>
    (simp only [copyRead, hk, hs, if_true]; cases selectSt n a <;> rfl)

/-- **`selectOnSaveEmptyDefault`** — a word member of the new struct is the word. -/
theorem selectOnCopyDefault {s n : Struct} {a : Seg} {x : PrimVal}
    (hn : NodeKind.isStructLike n.kind = true) (h : selectSt n a = .prim x) :
    selectSt (copyTo s [] (st n)) a = .prim x := by
  show copyRead s.kind n.kind _ _ a (selectSt s a) (selectSt n a) = _
  rcases structLike_cases hn with hk | hk <;> simp only [copyRead, hk, h, copyVal]

/-- **`selectOnSaveEmptyMap`** — a mapping copied over a mapping keeps the old
entries: Solidity copies no mapping. -/
theorem selectOnCopyMap {s n : Struct} {a : Seg}
    (hs : s.kind = some .map) (hn : n.kind = some .map) :
    selectSt (copyTo s [] (st n)) a = selectSt s a := by
  show copyRead s.kind n.kind _ _ a (selectSt s a) (selectSt n a) = _
  simp only [copyRead, hs, hn, if_true]

/-- **`selectOnSaveEmptyIndexStruct`**, the length — the new array's. -/
theorem selectOnCopySize {s n : Struct} {fx : Bool} (hn : n.kind = some (.arr fx)) :
    selectSt (copyTo s [] (st n)) lengthSeg = selectSt n lengthSeg := by
  show copyRead s.kind n.kind _ _ lengthSeg (selectSt s lengthSeg) (selectSt n lengthSeg) = _
  simp only [copyRead, hn, if_true]

/-- **`selectOnSaveEmptyIndexStruct`**, the in-bounds branch — an element the new
array has is copied over the old slot. -/
theorem selectOnCopyIndexNew {s n : Struct} {fx : Bool} {i : Int}
    (hs : NodeKind.isArr s.kind = true) (hn : n.kind = some (.arr fx))
    (h : inRange (lenOf n) i = true) :
    asStruct (selectSt (copyTo s [] (st n)) (.at i)) =
      copyTo (asStruct (selectSt s (.at i))) [] (selectSt n (.at i)) := by
  show asStruct (copyRead s.kind n.kind (lenOf s) (lenOf n) (.at i) (selectSt s (.at i))
    (selectSt n (.at i))) = _
  simp only [copyRead, hn, h, hs, if_true]
  cases selectSt n (.at i) <;> rfl

/-- **`selectOnSaveEmptyIndexStruct`**, the clear branch — a slot the old array
had and the new one does not is deleted.  No length invariant. -/
theorem selectOnCopyIndexClear {s n : Struct} {fx : Bool} {i : Int}
    (hs : NodeKind.isArr s.kind = true) (hn : n.kind = some (.arr fx))
    (h1 : inRange (lenOf n) i = false) (h2 : inRange (lenOf s) i = true) :
    selectSt (copyTo s [] (st n)) (.at i) = delValue (selectSt s (.at i)) := by
  show copyRead s.kind n.kind (lenOf s) (lenOf n) (.at i) (selectSt s (.at i))
    (selectSt n (.at i)) = _
  simp only [copyRead, hn, h1, h2, hs, Bool.and_self, if_true, Bool.false_eq_true, if_false]

/-- **`selectOnSaveEmptyIndexStruct`**, the keep branch — a slot past both lengths
is kept as it was.  No length invariant. -/
theorem selectOnCopyIndexKeep {s n : Struct} {fx : Bool} {i : Int}
    (hs : NodeKind.isArr s.kind = true) (hn : n.kind = some (.arr fx))
    (h1 : inRange (lenOf n) i = false) (h2 : inRange (lenOf s) i = false) :
    selectSt (copyTo s [] (st n)) (.at i) = selectSt s (.at i) := by
  show copyRead s.kind n.kind (lenOf s) (lenOf n) (.at i) (selectSt s (.at i))
    (selectSt n (.at i)) = _
  simp only [copyRead, hn, h1, h2, hs, Bool.and_false, if_true, Bool.false_eq_true, if_false]

/-- A node copied over a node of another shape lands on fresh slots: the old
node is not read (`SVal.strip`). -/
theorem selectOnCopyOther {o n : Struct} {a : Seg}
    (h : NodeKind.sameShape o.kind n.kind = false) :
    selectSt (.copyAt o n) a = selectSt (.copyAt .mtSt n) a := by
  show copyRead o.kind n.kind _ _ a (selectSt o a) (selectSt n a) =
    copyRead none n.kind _ _ a (st .mtSt) (selectSt n a)
  revert h
  cases n.kind with
  | none => intro h; simp only [copyRead, NodeKind.sameShape] at h ⊢; rw [h]; rfl
  | some k =>
    cases k with
    | struct => intro h; simp only [copyRead, NodeKind.sameShape] at h ⊢; rw [h]; rfl
    | map =>
      intro h
      simp only [NodeKind.sameShape] at h
      have h' : o.kind ≠ some .map := fun he => by rw [he] at h; exact absurd h (by decide)
      simp only [copyRead, h', if_false, reduceCtorEq]
    | arr fx =>
      intro h
      simp only [NodeKind.sameShape] at h
      rcases a with f | i
      · rfl
      · simp only [copyRead, h, Bool.false_and, Bool.false_eq_true, if_false]; rfl

/-! ## Push and pop

The `storagePush*`/`storagePop*` rules, read back at the slot and the
length they write. -/

/-- A path that leaves `q` still leaves it when extended. -/
private theorem diverges_append {p q : List Seg} (r : List Seg) (h : diverges p q = true) :
    diverges (p ++ r) q = true := by
  induction p generalizing q with
  | nil => simp only [diverges, Bool.false_eq_true] at h
  | cons a p' ih =>
    cases q with
    | nil => simp only [diverges, Bool.false_eq_true] at h
    | cons b q' =>
      simp only [diverges] at h
      simp only [List.cons_append, diverges]
      split
      · rw [if_pos ‹a = b›] at h; exact ih h
      · rfl

/-- The length and an element of one array are two different members. -/
private theorem diverges_len_at (p : List Seg) (i : Int) :
    diverges (p ++ [lengthSeg]) (p ++ [.at i]) = true := by
  induction p with
  | nil => rfl
  | cons a p' ih => simp only [List.cons_append, diverges, if_true, ih]

/-- `push(w)` stores `w` at the old length. -/
theorem find_pushT_slot (s : Struct) (p : List Seg) (w : StValue) :
    findSt (pushT s p w) (p ++ [.at (lenAt s p)]) = w := by
  rw [pushT, find_save_frame _ _ _ _ (diverges_len_at p _)]
  exact find_save_same _ (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil _ _)) _

/-- `push(w)` grows the length by one. -/
theorem find_pushT_len (s : Struct) (p : List Seg) (w : StValue) :
    findSt (pushT s p w) (p ++ [lengthSeg]) = int (lenAt s p + 1) :=
  find_save_same _ (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil _ _)) _

/-- A read off the array's path does not see a `push`. -/
theorem find_pushT_frame (s : Struct) (w : StValue) {p q : List Seg} (h : diverges p q = true) :
    findSt (pushT s p w) q = findSt s q := by
  rw [pushT, find_save_frame _ _ _ _ (diverges_append _ h),
    find_save_frame _ _ _ _ (diverges_append _ h)]

/-- `pop()` deletes the last element. -/
theorem find_popT_slot (s : Struct) (p : List Seg) :
    findSt (popT s p) (p ++ [.at (lenAt s p - 1)]) =
      delValue (findSt s (p ++ [.at (lenAt s p - 1)])) := by
  rw [popT, find_save_frame _ _ _ _ (diverges_len_at p _)]
  exact find_delAt_same _ (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil _ _))

/-- `pop()` shrinks the length by one. -/
theorem find_popT_len (s : Struct) (p : List Seg) :
    findSt (popT s p) (p ++ [lengthSeg]) = int (lenAt s p - 1) :=
  find_save_same _ (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil _ _)) _

/-- A read off the array's path does not see a `pop`. -/
theorem find_popT_frame (s : Struct) {p q : List Seg} (h : diverges p q = true) :
    findSt (popT s p) q = findSt s q := by
  rw [popT, find_save_frame _ _ _ _ (diverges_append _ h),
    find_delAt_frame _ (diverges_append _ h)]

/-- The shrink writes the length alone. -/
theorem find_shrinkT_len (s : Struct) (p : List Seg) :
    findSt (shrinkT s p) (p ++ [lengthSeg]) = int (lenAt s p - 1) :=
  find_save_same _ (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil _ _)) _

/-- At a primitive element type a bare `push()` lands on the default. -/
theorem fillSlot_prim (d v : StValue) : fillSlot true d v = d := rfl

/-- Where no slot ever was, a bare `push()` lands on the default. -/
theorem fillSlot_absent (b : Bool) (d : StValue) {s : Struct} (h : s.kind = none) :
    fillSlot b d (.st s) = d := by
  cases b <;> simp only [fillSlot, h, if_true, Bool.false_eq_true, if_false]

/-- A slot a `pop` left behind is recycled as it is. -/
theorem fillSlot_recycled (d : StValue) {s : Struct} (h : s.kind ≠ none) :
    fillSlot false d (.st s) = .st s := by
  simp only [fillSlot, h, Bool.false_eq_true, if_false]

end StValue
end Theory
end Solidity
