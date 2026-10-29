import Solidity.Source.Types
import Solidity.Roadmap.Contracts

/-!
# Source state (S04.01)

The independent source state, intrinsic in the static types of S01
(`Solidity/Source/Types.lean`), over a `Layout` read off the declaration
graph (struct fields, enum sizes, the underlying type of each user-defined
value type):

- `Val D τ`: a value of type `τ`. Integers and fixed-point values carry
  their range, `bytesN` its length, an enum value is below the enum's size,
  a user-defined value is a value of its underlying type, and an external
  function's selector has four bytes.  A reference exists only at a
  reference type of its location (`STy.loc?`): a `memory` address, a
  logical `storage` path or a `calldata` offset;
- `Data D τ`: the contents of a reference type.  An array is its length
  (the declared one, for a static array) and its elements, a struct its
  fields, `bytes`/`string` their bytes, and a mapping a total function from
  key *contents* (`KeyOf`: the bytes of a `bytes`/`string` key, the value of
  a value-type key) to values, so two copies of one string are one key.
  Recursive structs through mappings and dynamic arrays are allowed, as in
  solc: `Data` is inductive over the contents, not the type;
- `Heap D`: `memory`, typed contents at addresses below `next`.  An element
  of reference type inside a `memory` aggregate is `Data.val` of a `memRef`,
  a pointer, so nested aliasing is expressible (`StateExamples.alias_seen`);
- `Calldata D`: the input and its decoded objects, read only (no operation
  writes it);
- `Storage D L`: persistent storage over a layout `L : SPath → STy` giving
  each logical path its declared type; a path holds a value of exactly that
  type, or the default (G04 Q2: the *logical* aliasing of storage
  references is fixed, the physical packing is not observable).

**Identity and copy.**  A `memory` reference is an address: a write through
it is seen through every equal reference (`Heap.write_get`) and through no
other (`Heap.write_other`), and keeps every cell's type (`Heap.write_ty`).
A copy into `memory` allocates a fresh address holding equal contents
(`Heap.copy_get`), and later writes through the copy leave the source
(`Heap.copy_independent`).  `storage` references are logical paths; a write
through one path is seen through it and through no other
(`Storage.write_read`, `Storage.write_other`).

Nothing here reads the compiler or the intrinsic semantics.
-/

namespace Solidity.Source

open Solidity.Roadmap (Address Word)

/-- What values read from the declaration graph. -/
structure Layout where
  /-- The field types of each struct. -/
  fields : DeclName → List STy
  /-- The number of members of each enum. -/
  enumSize : DeclName → Nat
  /-- The underlying (elementary) type of each user-defined value type. -/
  underlying : DeclName → STy

/-- The data location of a reference type (`storage` for a mapping). -/
def STy.loc? : STy → Option DataLoc
  | .bytes l | .string l | .array l _ _ | .struct l _ => some l
  | .mapping _ _ => some .storage
  | _ => none

/-- A step below a state variable: an array index, a struct field by
position, a mapping key by its contents' bytes. -/
inductive Step where
  | index (i : Nat)
  | field (i : Nat)
  | key (bs : List UInt8)
  deriving DecidableEq, Repr

/-- A logical storage path: a state variable and the steps below it. -/
structure SPath where
  root : DeclName
  steps : List Step
  deriving DecidableEq, Repr

/-- A value of type `τ`, its invariants part of it. -/
inductive Val (D : Layout) : STy → Type where
  | int {t : IntTy} (v : Int) (h : t.lo ≤ v ∧ v ≤ t.hi) : Val D (.int t)
  | bool (b : Bool) : Val D .bool
  | address {p : Bool} (a : Address) : Val D (.address p)
  | fixedBytes {n : Nat} {h : 1 ≤ n ∧ n ≤ 32} (bs : List UInt8) (hl : bs.length = n) :
      Val D (.fixedBytes n h)
  | fixed {f : FixTy} (v : Int) (h : f.lo ≤ v ∧ v ≤ f.hi) : Val D (.fixed f)
  | enum {d : DeclName} (i : Fin (D.enumSize d)) : Val D (.enum d)
  | udvt {d : DeclName} (v : Val D (D.underlying d)) : Val D (.udvt d)
  | contract {d : DeclName} (a : Address) : Val D (.contract d)
  /-- An internal function value: the function's declaration. -/
  | internalFn {ps rs : List STy} {m : Option Mutability} (d : DeclName) : Val D (.fn false ps rs m)
  /-- An external function value: an address and a four-byte selector. -/
  | externalFn {ps rs : List STy} {m : Option Mutability} (a : Address) (sel : List UInt8)
      (hs : sel.length = 4) : Val D (.fn true ps rs m)
  | memRef {τ : STy} (h : τ.loc? = some .memory) (addr : Nat) : Val D τ
  | storRef {τ : STy} (h : τ.loc? = some .storage) (p : SPath) : Val D τ
  | cdRef {τ : STy} (h : τ.loc? = some .calldata) (off : Nat) : Val D τ

/-- The key contents of a mapping's key type: bytes for `bytes`/`string`,
the value otherwise. -/
def KeyOf (D : Layout) : STy → Type
  | .bytes _ | .string _ => List UInt8
  | τ => Val D τ

mutual

/-- The contents of a reference type. -/
inductive Data (D : Layout) : STy → Type where
  /-- A value, or a pointer to an object of reference type. -/
  | val {τ : STy} (v : Val D τ) : Data D τ
  | bytes {l : DataLoc} (bs : List UInt8) : Data D (.bytes l)
  | string {l : DataLoc} (bs : List UInt8) : Data D (.string l)
  /-- `len` elements; a static array has its declared length. -/
  | array {l : DataLoc} {τ : STy} {n : Option Nat} (len : Nat) (hl : ∀ m, n = some m → m = len)
      (xs : Fin len → Data D τ) : Data D (.array l τ n)
  | struct {l : DataLoc} {d : DeclName} (fs : DataList D (D.fields d)) : Data D (.struct l d)
  /-- A mapping: every key's contents has a value (absent keys hold the default). -/
  | mapping {k v : STy} (m : KeyOf D k → Data D v) : Data D (.mapping k v)

/-- The contents of a list of fields. -/
inductive DataList (D : Layout) : List STy → Type where
  | nil : DataList D []
  | cons {τ : STy} {τs : List STy} : Data D τ → DataList D τs → DataList D (τ :: τs)

end

/-! ## Defaults -/

/-- Zero is in the range of every integer type. -/
theorem IntTy.zero_mem (t : IntTy) : t.lo ≤ 0 ∧ 0 ≤ t.hi := by
  unfold IntTy.lo IntTy.hi
  have h1 := Int.natCast_nonneg (2 ^ (t.bits - 1))
  have h2 := Int.natCast_nonneg (2 ^ (t.bits - 1) - 1)
  have h3 := Int.natCast_nonneg (2 ^ t.bits - 1)
  split <;> omega

/-- Zero is in the range of every fixed-point type. -/
theorem FixTy.zero_mem (t : FixTy) : t.lo ≤ 0 ∧ 0 ≤ t.hi := by
  unfold FixTy.lo FixTy.hi
  have h1 := Int.natCast_nonneg (2 ^ (t.bits - 1))
  have h2 := Int.natCast_nonneg (2 ^ (t.bits - 1) - 1)
  have h3 := Int.natCast_nonneg (2 ^ t.bits - 1)
  split <;> omega

/-- The default of an elementary type (other than a user-defined one). -/
def Val.defaultElem (D : Layout) : (τ : STy) → Option (Val D τ)
  | .int t => some (.int 0 t.zero_mem)
  | .bool => some (.bool false)
  | .address _ => some (.address Address.zero)
  | .fixedBytes n _ => some (.fixedBytes (List.replicate n 0) (List.length_replicate ..))
  | .fixed f => some (.fixed 0 f.zero_mem)
  | .contract _ => some (.contract Address.zero)
  | _ => none

/-- **The default value** of a value type (what a declaration without an
initializer, `delete`, and an unwritten storage path hold): zero, `false`,
the zero address, zero bytes, the first enum member, the underlying
default; `none` for reference types, whose default is a fresh zeroed
object, and for function types, whose default is a panicking function
(S02). -/
def Val.default (D : Layout) : (τ : STy) → Option (Val D τ)
  | .enum d => if h : 0 < D.enumSize d then some (.enum ⟨0, h⟩) else none
  | .udvt d => (Val.defaultElem D (D.underlying d)).map .udvt
  | τ => Val.defaultElem D τ

/-! ## Calldata -/

/-- `calldata`: the input bytes and the decoded objects at their offsets.
There is no write operation: calldata is read only by construction.  The
decoding of `input` into `objects` is the ABI decoder's (S04.04 with the
ABI work), not fixed here. -/
structure Calldata (D : Layout) where
  input : List UInt8
  objects : Nat → Option (Σ τ, Data D τ)

/-! ## Memory -/

/-- `memory`: typed contents at addresses below `next`. -/
structure Heap (D : Layout) where
  cells : Nat → Option (Σ τ, Data D τ)
  next : Nat
  bounded : ∀ a, next ≤ a → cells a = none

namespace Heap

variable {D : Layout}

/-- The empty heap. -/
def empty : Heap D := ⟨fun _ => none, 0, fun _ _ => rfl⟩

/-- The contents at an address. -/
def get (h : Heap D) (a : Nat) : Option (Σ τ, Data D τ) := h.cells a

/-- The type of the object at an address. -/
def ty (h : Heap D) (a : Nat) : Option STy := (h.cells a).map Sigma.fst

/-- **Allocation**: fresh contents at `next`. -/
def alloc (h : Heap D) (x : Σ τ, Data D τ) : Heap D × Nat :=
  ({ cells := fun a => if a = h.next then some x else h.cells a, next := h.next + 1,
     bounded := fun a ha => by
       have hne : a ≠ h.next := by omega
       simp only [hne, if_false]
       exact h.bounded a (by omega) }, h.next)

/-- A write through a reference, at the object's own type. -/
def write (h : Heap D) (a : Nat) {τ : STy} (x : Data D τ) (hty : h.ty a = some τ) : Heap D :=
  { cells := fun b => if b = a then some ⟨τ, x⟩ else h.cells b, next := h.next,
    bounded := fun b hb => by
      have hne : b ≠ a := by
        intro e
        subst e
        simp only [ty, h.bounded b hb, Option.map_none, reduceCtorEq] at hty
      simp only [hne, if_false]
      exact h.bounded b hb }

/-- **A copy into memory**: a fresh object with the source's contents. -/
def copy (h : Heap D) (src : Nat) : Option (Heap D × Nat) := (h.get src).map h.alloc

/-- The allocated address was free. -/
theorem alloc_fresh (h : Heap D) (x : Σ τ, Data D τ) : h.get (h.alloc x).2 = none :=
  h.bounded _ (Nat.le_refl _)

/-- The allocated address holds the contents. -/
theorem alloc_get (h : Heap D) (x : Σ τ, Data D τ) : (h.alloc x).1.get (h.alloc x).2 = some x := by
  simp only [alloc, get, if_true]

/-- Allocation changes no other address. -/
theorem alloc_other (h : Heap D) (x : Σ τ, Data D τ) {a : Nat} (ha : a ≠ (h.alloc x).2) :
    (h.alloc x).1.get a = h.get a := by
  simp only [alloc, get] at ha ⊢
  simp only [ha, if_false]

/-- **Aliasing**: a write through an address is seen through it. -/
theorem write_get (h : Heap D) (a : Nat) {τ : STy} (x : Data D τ) (hty : h.ty a = some τ) :
    (h.write a x hty).get a = some ⟨τ, x⟩ := by
  simp only [write, get, if_true]

/-- A write through one address is invisible through another. -/
theorem write_other (h : Heap D) {a b : Nat} (hab : b ≠ a) {τ : STy} (x : Data D τ)
    (hty : h.ty a = some τ) : (h.write a x hty).get b = h.get b := by
  simp only [write, get, hab, if_false]

/-- **A write keeps every object's type.** -/
theorem write_ty (h : Heap D) (a b : Nat) {τ : STy} (x : Data D τ) (hty : h.ty a = some τ) :
    (h.write a x hty).ty b = h.ty b := by
  simp only [write, ty]
  split
  · rename_i e
    subst e
    simp only [Option.map_some]
    exact hty.symm
  · rfl

/-- **A copy holds the source's contents**, at a fresh address. -/
theorem copy_get (h : Heap D) {src : Nat} {x : Σ τ, Data D τ} (hs : h.get src = some x) :
    ∃ h' a, h.copy src = some (h', a) ∧ h'.get a = some x ∧ h.get a = none :=
  ⟨(h.alloc x).1, (h.alloc x).2, by simp only [copy, hs, Option.map_some], alloc_get h x, alloc_fresh h x⟩

/-- **A copy is independent of its source**: writing the copy leaves the
source's contents. -/
theorem copy_independent (h : Heap D) {src : Nat} {x : Σ τ, Data D τ} (hs : h.get src = some x)
    {τ : STy} (y : Data D τ) (hty : (h.alloc x).1.ty (h.alloc x).2 = some τ) :
    (((h.alloc x).1).write (h.alloc x).2 y hty).get src = some x := by
  have hlt : src < h.next := by
    refine Nat.lt_of_not_le fun hn => ?_
    have e := h.bounded src hn
    simp only [get] at hs
    rw [e] at hs
    cases hs
  have hne : src ≠ (h.alloc x).2 := by simp only [alloc]; omega
  rw [write_other _ hne, alloc_other _ _ hne, hs]

end Heap

/-! ## Storage -/

/-- Persistent storage over the layout `L`: the value written at each
path, at the path's declared type (`none`: never written, read as the
default). -/
structure Storage (D : Layout) (L : SPath → STy) where
  cell : (p : SPath) → Option (Val D (L p))

namespace Storage

variable {D : Layout} {L : SPath → STy}

/-- The empty storage: every path holds the default. -/
def empty : Storage D L := ⟨fun _ => none⟩

/-- The value at a path: the written one, or the default of its type. -/
def read (s : Storage D L) (p : SPath) : Option (Val D (L p)) :=
  match s.cell p with
  | some v => some v
  | none => Val.default D (L p)

/-- An unwritten path reads the default. -/
theorem read_empty (p : SPath) : (empty : Storage D L).read p = Val.default D (L p) := rfl

/-- Setting a path's cell (`none` clears it). -/
def set (s : Storage D L) (p : SPath) (o : Option (Val D (L p))) : Storage D L :=
  ⟨fun q => if h : q = p then h ▸ o else s.cell q⟩

/-- A write at a path. -/
def write (s : Storage D L) (p : SPath) (v : Val D (L p)) : Storage D L := s.set p (some v)

/-- **A write reads back.** -/
theorem write_read (s : Storage D L) (p : SPath) (v : Val D (L p)) : (s.write p v).read p = some v := by
  simp only [write, set, read, dif_pos]

/-- A write is invisible through every other path. -/
theorem write_other (s : Storage D L) {p q : SPath} (h : q ≠ p) (v : Val D (L p)) :
    (s.write p v).read q = s.read q := by
  simp only [write, set, read, h, dif_neg, not_false_eq_true]

/-- Restoring a path's old cell undoes a set. -/
theorem set_restore (s : Storage D L) (p : SPath) (o : Option (Val D (L p))) :
    (s.set p o).set p (s.cell p) = s := by
  cases s with
  | mk c =>
    simp only [set, mk.injEq]
    funext q
    by_cases h : q = p
    · subst h; simp only [dif_pos]
    · simp only [h, dif_neg, not_false_eq_true]

end Storage

end Solidity.Source
