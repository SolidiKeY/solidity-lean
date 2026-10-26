import Solidity.TypeGraph
import Solidity.Semantics.Value

/-!
Typed well-founded storage values for a finite declaration graph. Slots
are functions over finite index/key domains. They support demand-driven
reads and pointwise writes and deletion; they do not provide an efficient
enumeration or executable equality of whole mappings. Missing slots use
the type's default only when observed.

An array distinguishes its live word length from its retained extent,
a one-past-end cardinality. A retained slot is still observable after pop.
-/

namespace Solidity.TypeGraph

abbrev Extent := Fin (2 ^ 256 + 1)

mutual
inductive Value {n : Nat} (G : Schema n) : Ty n → Type where
  | prim {p : PrimTy} (value : p.Denote) : Value G (.prim p)
  | node {i : Fin n} (fields : {T : Ty n} → Field (G.fields i) T → Value G T) : Value G (.node i)
  | array {E : Ty n} (extent : Extent) (length : Index)
      (live_le : length.val ≤ extent.val)
      (slots : Fin extent.val → Slot G E) : Value G (.array E)
  | fixed {E : Ty n} {m : FixedSize} (slots : Fin m.val → Slot G E) :
      Value G (.fixed E m)
  | mapping {K : PrimTy} {V : Ty n} (slots : K.Denote → Slot G V) :
      Value G (.mapping K V)

inductive Slot {n : Nat} (G : Schema n) : Ty n → Type where
  | absent {T : Ty n} : Slot G T
  | present {T : Ty n} (value : Value G T) : Slot G T
end

def Slot.getD {n : Nat} {G : Schema n} {T : Ty n}
    (slot : Slot G T) (dflt : Value G T) : Value G T :=
  match slot with
  | .absent => dflt
  | .present v => v

abbrev Fields {n : Nat} (G : Schema n) (fs : List (Name × Ty n)) :=
  {T : Ty n} → Field fs T → Value G T

def Fields.get {n : Nat} {G : Schema n} {fs : List (Name × Ty n)}
    {T : Ty n} (fields : Fields G fs) (p : Field fs T) : Value G T := fields p

def Fields.set {n : Nat} {G : Schema n} {fs : List (Name × Ty n)}
    {T : Ty n} (fields : Fields G fs) (p : Field fs T) (value : Value G T) :
    Fields G fs :=
  fun {U} q =>
    if h : q.toNat = p.toNat then
      cast (congrArg (Value G) (Field.type_eq q p h).symm) value
    else fields q

theorem Fields.get_set {n : Nat} {G : Schema n}
    {fs : List (Name × Ty n)} {T : Ty n} (vs : Fields G fs)
    (p : Field fs T) (v : Value G T) : Fields.get (Fields.set vs p v) p = v := by
  simp only [Fields.get, Fields.set, dif_pos rfl]
  rfl

theorem Fields.get_set_other {n : Nat} {G : Schema n}
    {fs : List (Name × Ty n)} {T U : Ty n} (vs : Fields G fs)
    (p : Field fs T) (q : Field fs U) (v : Value G T)
    (h : q.toNat ≠ p.toNat) : Fields.get (Fields.set vs p v) q = Fields.get vs q :=
  dif_neg h

def Slots.write {K : Type} [DecidableEq K] {n : Nat} {G : Schema n} {E : Ty n}
    (slots : K → Slot G E) (key : K) (value : Value G E) : K → Slot G E :=
  fun k => if k = key then .present value else slots k

theorem Slots.write_self {K : Type} [DecidableEq K] {n : Nat}
    {G : Schema n} {E : Ty n} (slots : K → Slot G E) (key : K)
    (value : Value G E) : Slots.write slots key value key = .present value := by
  exact if_pos rfl

theorem Slots.write_other {K : Type} [DecidableEq K] {n : Nat}
    {G : Schema n} {E : Ty n} (slots : K → Slot G E) (key other : K)
    (h : other ≠ key) (value : Value G E) :
    Slots.write slots key value other = slots other := by
  simp only [Slots.write, if_neg h]

def Value.extent {n : Nat} {G : Schema n} {E : Ty n} :
    Value G (.array E) → Extent
  | .array extent _ _ _ => extent

def Value.length {n : Nat} {G : Schema n} {E : Ty n} :
    Value G (.array E) → Index
  | .array _ length _ _ => length

def Value.slots {n : Nat} {G : Schema n} {E : Ty n}
    (v : Value G (.array E)) : Fin v.extent.val → Slot G E :=
  match v with
  | .array _ _ _ slots => slots

end Solidity.TypeGraph
