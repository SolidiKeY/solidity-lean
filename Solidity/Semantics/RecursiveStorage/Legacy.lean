import Solidity.Semantics.RecursiveStorage.Admission
import Solidity.Semantics.Storage.Ops

/-!
An intrinsic compatibility interface with the ordinary interpreter's `SVal`.
A finite `Layout` relates an existing type to a graph type; struct layouts
retain ordered field names and types. It is evidence, not an unchecked cast.
Recursive graph nodes cannot have a finite legacy layout, but their acyclic
subtrees can receive ordinary storage values through `writeLegacy`.

Legacy mappings can have arbitrary defaults. Every key is represented by a
present slot containing its actual legacy lookup, including the fallback.
Legacy arrays may have more than a word's worth of raw shadows: the graph
caps their extent at 2^256. Every representable index is retained. There is
no claim of equality of uncapped raw extents or of whole-value equality.
-/

namespace Solidity.TypeGraph.Legacy

mutual
/-- A finite, shape-preserving realization of an ordinary storage type. -/
inductive Layout {n : Nat} (G : Schema n) : Solidity.Ty → Ty n → Type where
  | prim (p : PrimTy) : Layout G (.prim p) (.prim p)
  | node {s : Name} {i : Fin n}
      (fields : FieldLayouts G (Semantics.structDef s) (G.fields i)) :
      Layout G (.ref (.struct s)) (.node i)
  | array {A : Solidity.Ty} {B : Ty n} (elem : Layout G A B) :
      Layout G (.ref (.array A)) (.array B)
  | fixed {A : Solidity.Ty} {B : Ty n} (elem : Layout G A B) (size : FixedSize) :
      Layout G (.ref (.fixed A size.val)) (.fixed B size)
  | mapping {A : Solidity.Ty} {B : Ty n} (key : PrimTy) (value : Layout G A B) :
      Layout G (.ref (.mapping key A)) (.mapping key B)

/-- Both field lists have the same names, order and related intrinsic types. -/
inductive FieldLayouts {n : Nat} (G : Schema n) :
    List (Name × Solidity.Ty) → List (Name × Ty n) → Type where
  | nil : FieldLayouts G [] []
  | cons {f : Name} {A : Solidity.Ty} {B : Ty n}
      {as : List (Name × Solidity.Ty)} {bs : List (Name × Ty n)}
      (head : Layout G A B) (tail : FieldLayouts G as bs) :
      FieldLayouts G ((f, A) :: as) ((f, B) :: bs)
end

mutual
/-- Embed an ordinary typed value without assuming canonical mapping defaults.
Recursion follows the finite layout; it never unfolds graph cycles. -/
def Layout.encode {n : Nat} {G : Schema n} :
    {A : Solidity.Ty} → {B : Ty n} → Layout G A B → SVal A → Value G B
  | _, _, .prim _, v => .prim v.view
  | _, _, .node fields, v => .node (FieldLayouts.encode fields v.view)
  | _, _, .array elem, v =>
    let w : ArrView _ := v.view
    let all := w.elems.toList ++ w.shadow.toList
    .array ⟨min all.length (2 ^ 256), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      ⟨w.n, w.hn⟩
      (by
        change w.n ≤ min (w.elems.toList ++ w.shadow.toList).length (2 ^ 256)
        apply Nat.le_min_of_le_of_le
        · rw [List.length_append, SVec.length_toList]
          omega
        · exact Nat.le_of_lt w.hn)
      (fun i => match all[i.val]? with
        | none => .absent
        | some x => .present (Layout.encode elem x))
  | _, _, .fixed elem size, v =>
    .fixed (fun i : Fin size.val => match (v.view : SVec _ size.val).toList[i.val]? with
      | none => .absent
      | some x => .present (Layout.encode elem x))
  | _, _, .mapping _ value, v =>
    let w : SMap _ _ × SVal _ := v.view
    .mapping (fun k => .present
      (Layout.encode value ((Semantics.lookupBy k w.1.toList).getD w.2)))

def FieldLayouts.encode {n : Nat} {G : Schema n} :
    {as : List (Name × Solidity.Ty)} → {bs : List (Name × Ty n)} →
    FieldLayouts G as bs → SFields as → Fields G bs
  | _, _, .nil, _ => fun p => nomatch p
  | _, _, .cons head tail, vs => fun p =>
    match p with
    | .here => Layout.encode head vs.view.1
    | .there q => FieldLayouts.encode tail vs.view.2 q
end

/-- Assign an ordinary interpreter value into an acyclic subtree of a recursive
root. This calls the graph copy/write API, including mapping barriers. -/
def writeLegacy {n : Nat} {G : Schema n} {R B : Ty n} {A : Solidity.Ty}
    (root : Value G R) (dst : Path G R B) (layout : Layout G A B) (src : SVal A) :
    Option (Value G R) := root.write dst (layout.encode src)

/-- The source-assignment variant also requires the checked recursive copy
policy. `writeLegacy` is the internal algebraic operation. -/
def assignLegacy {n : Nat} {G : Schema n} {R B : Ty n} {A : Solidity.Ty}
    (root : Value G R) (dst : Path G R B) (permit : CopyPermit G B)
    (layout : Layout G A B) (src : SVal A) : Option (Value G R) :=
  root.assign dst permit (layout.encode src)

/-- Read-back connects the ordinary typed source to the graph assignment API. -/
theorem find_writeLegacy {n : Nat} {G : Schema n} {R B : Ty n} {A : Solidity.Ty}
    (root result : Value G R) (dst : Path G R B) (layout : Layout G A B)
    (src : SVal A) (old : Value G B) (read : root.find dst = some old)
    (written : writeLegacy root dst layout src = some result) :
    result.find dst = some (old.overlay (layout.encode src)) :=
  root.find_write result dst (layout.encode src) old read written

/-- The mapping bridge agrees with the ordinary interpreter at every key,
including unwritten keys with a noncanonical legacy fallback. -/
theorem Layout.read_key {n : Nat} {G : Schema n} {A : Solidity.Ty} {B : Ty n}
    (layout : Layout G A B) (K : PrimTy) (m : SMap K A) (d : SVal A)
    (k : K.Denote) :
    ((Layout.mapping K layout).encode (SVal.map m d)).find
        (.cons (.key k) .nil) =
      ((SVal.map m d).find (.key k .nil)).map layout.encode := by
  rw [SVal.find_key]
  change some (layout.encode ((Semantics.lookupBy k m.toList).getD d)) = _
  cases Semantics.lookupBy k m.toList <;> rfl

/-- A finite sequence of mapping reads on the two representations. The endpoint
layout is carried in the type; no erased or untyped intermediate value occurs. -/
inductive KeyPath {n : Nat} {G : Schema n} :
    {A U : Solidity.Ty} → {B V : Ty n} → Layout G A B → Layout G U V → Type where
  | nil {A : Solidity.Ty} {B : Ty n} {layout : Layout G A B} : KeyPath layout layout
  | key {A U : Solidity.Ty} {B V : Ty n} {layout : Layout G A B}
      {leaf : Layout G U V} (K : PrimTy) (k : K.Denote) (rest : KeyPath layout leaf) :
      KeyPath (Layout.mapping K layout) leaf

def KeyPath.legacy {n : Nat} {G : Schema n} :
    {A U : Solidity.Ty} → {B V : Ty n} → {layout : Layout G A B} → {leaf : Layout G U V} →
    KeyPath layout leaf → Solidity.Path A U
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .key _ k rest => .key k rest.legacy

def KeyPath.graph {n : Nat} {G : Schema n} :
    {A U : Solidity.Ty} → {B V : Ty n} → {layout : Layout G A B} → {leaf : Layout G U V} →
    KeyPath layout leaf → Path G B V
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .key _ k rest => .cons (.key k) rest.graph

/-- Ordinary `SVal.find` and graph `find` commute along every typed mapping
path, with arbitrary stored entries and defaults at all levels. -/
theorem KeyPath.find_encode {n : Nat} {G : Schema n}
    {A U : Solidity.Ty} {B V : Ty n} {layout : Layout G A B} {leaf : Layout G U V}
    (path : KeyPath layout leaf) (src : SVal A) :
    (layout.encode src).find path.graph = (src.find path.legacy).map leaf.encode := by
  induction path with
  | nil => rfl
  | key K k rest ih =>
    cases src with
    | map m d =>
      rw [KeyPath.legacy, SVal.find_key]
      simp only [KeyPath.graph, Layout.encode, Value.find, Path.read, Step.get,
        Slot.getD, SVal.view, Option.bind_some]
      cases h : Semantics.lookupBy k m.toList with
      | none => simpa only [Value.find, h, Option.getD_none] using ih d
      | some v => simpa only [Value.find, h, Option.getD_some] using ih v

/-- The same correspondence for typed head observations (words, lengths and
capped extents), without claiming raw structural equality with legacy values. -/
theorem KeyPath.observe_encode {n : Nat} {G : Schema n}
    {A U : Solidity.Ty} {B V : Ty n} {layout : Layout G A B} {leaf : Layout G U V}
    (path : KeyPath layout leaf) (src : SVal A) :
    (layout.encode src).observe path.graph =
      (src.find path.legacy).map (fun v => (leaf.encode v).head) := by
  unfold Value.observe
  rw [path.find_encode]
  cases src.find path.legacy <;> rfl

end Solidity.TypeGraph.Legacy
