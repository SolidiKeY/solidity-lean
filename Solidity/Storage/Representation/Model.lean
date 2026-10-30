import Solidity.Storage.HashedLayout
import Solidity.Semantics.Storage.Ops

/-!
# Intrinsic values represented by symbolic storage

The source values and reads are the existing intrinsic `SVal` and `find`.
This relation does not define a source read by executing an encoder.
Mapping headers have no observable content; array shadows are represented
as well as their live prefixes. Packing and recursive declaration graphs
are separate obligations, not additional constructors of `STy`.
-/
namespace Solidity.Storage.Representation

abbrev Store : Type := Loc → Semantics.Word

mutual
/-- A layout shape is fixed independently of the particular stored value. -/
inductive TypeRep : Ty → STy → Prop where
  | scalar (p : PrimTy) : TypeRep (.prim p) .word
  | strct (s : Name) (ts : List STy)
      (fields : FieldTypesRep (Semantics.structDef s) ts) :
      TypeRep (.ref (.struct s)) (.strct ts)
  | fixed {E : Ty} {t : STy} (n : Nat) (elem : TypeRep E t) :
      TypeRep (.ref (.fixed E n)) (.sarr t n)
  | array {E : Ty} {t : STy} (elem : TypeRep E t) :
      TypeRep (.ref (.array E)) (.darr t)
  | mapping {V : Ty} {t : STy} (K : PrimTy) (value : TypeRep V t) :
      TypeRep (.ref (.mapping K V)) (.map t)

inductive FieldTypesRep : List (Name × Ty) → List STy → Prop where
  | nil : FieldTypesRep [] []
  | cons {f : Name} {T : Ty} {fs : List (Name × Ty)} {t : STy} {ts : List STy}
      (head : TypeRep T t) (tail : FieldTypesRep fs ts) :
      FieldTypesRep ((f, T) :: fs) (t :: ts)
end

mutual
/-- A typed source value represented at an existing layout location. -/
inductive ValueRep : {T : Ty} → SVal T → STy → Loc → Store → Prop where
  | scalar {p : PrimTy} (v : p.Denote) (l : Loc) (w : Store)
      (read : w l = PrimTy.toWord v) : ValueRep (.prim v) .word l w
  | strct {s : Name} (fs : SFields (Semantics.structDef s))
      (ts : List STy) (l : Loc) (w : Store)
      (fields : FieldsRep fs ts l w) : ValueRep (.struct (s := s) fs) (.strct ts) l w
  | fixed {E : Ty} {n : Nat} (vs : SVec E n) (t : STy) (l : Loc) (w : Store)
      (shape : TypeRep E t)
      (elements : ElementsRep vs.toList t l w) : ValueRep (.fixed vs) (.sarr t n) l w
  | array {E : Ty} {n : Nat} (vs : SVec E n) (shadow : SList E)
      (hn : n < 2 ^ 256) (t : STy) (l : Loc) (w : Store)
      (shape : TypeRep E t)
      (live_bound : n ≤ lmax)
      (extent_bound : (vs.toList ++ shadow.toList).length ≤ lmax)
      (header : (w l).val = n)
      (elements : ElementsRep (vs.toList ++ shadow.toList) t (.data l 0) w) :
      ValueRep (.array vs shadow hn) (.darr t) l w
  | mapping {K : PrimTy} {V : Ty} (entries : SMap K V) (fallback : SVal V)
      (t : STy) (l : Loc) (w : Store)
      (shape : TypeRep V t)
      (values : ∀ k : K.Denote,
        ValueRep ((Semantics.lookupBy k entries.toList).getD fallback) t
          (.hash (PrimTy.toWord k).val.toNat l 0) w) :
      ValueRep (.map entries fallback) (.map t) l w

/-- Member types stay paired with their existing intrinsically typed values. -/
inductive FieldsRep : {fs : List (Name × Ty)} → SFields fs → List STy → Loc → Store → Prop where
  | nil (l : Loc) (w : Store) : FieldsRep .nil [] l w
  | cons {f : Name} {T : Ty} {fs : List (Name × Ty)}
      (v : SVal T) (rest : SFields fs) (t : STy) (ts : List STy) (l : Loc) (w : Store)
      (head : ValueRep v t l w) (tail : FieldsRep rest ts (l.add t.size) w) :
      FieldsRep (SFields.cons (f := f) v rest) (t :: ts) l w

/-- Physical slots include stale dynamic-array elements past the live end. -/
inductive ElementsRep : {E : Ty} → List (SVal E) → STy → Loc → Store → Prop where
  | nil {E : Ty} (t : STy) (l : Loc) (w : Store) : ElementsRep (E := E) [] t l w
  | cons {E : Ty} (v : SVal E) (rest : List (SVal E)) (t : STy) (l : Loc) (w : Store)
      (head : ValueRep v t l w) (tail : ElementsRep rest t (l.add t.size) w) :
      ElementsRep (v :: rest) t l w
end

/-- Every represented value has a value-independent layout shape. -/
theorem ValueRep.type {T : Ty} {v : SVal T} {t : STy} {l : Loc} {w : Store}
    (h : ValueRep v t l w) : TypeRep T t :=
  ValueRep.rec (motive_1 := fun {T} _ t _ _ _ => TypeRep T t)
    (motive_2 := fun {fs} _ ts _ _ _ => FieldTypesRep fs ts)
    (motive_3 := fun _ _ _ _ _ => True)
    (fun {p} _ _ _ _ => TypeRep.scalar p)
    (fun {s} _ ts _ _ _ ih => TypeRep.strct s ts ih)
    (fun {_ n} _ _ _ _ shape _ _ => TypeRep.fixed n shape)
    (fun {_ _} _ _ _ _ _ _ shape _ _ _ _ _ => TypeRep.array shape)
    (fun {K _} _ _ _ _ _ shape _ _ => TypeRep.mapping K shape)
    (fun _ _ => FieldTypesRep.nil)
    (fun {_ _ _} _ _ _ _ _ _ _ _ ih it => FieldTypesRep.cons ih it)
    (fun {_} _ _ _ => True.intro)
    (fun {_} _ _ _ _ _ _ _ _ _ => True.intro) h

/-- The existing contract store is its intrinsic field family, not an erased map. -/
abbrev StoreRep {C : Contract} (st : Solidity.Storage C) (ts : List STy)
    (l : Loc) (w : Store) : Prop := FieldsRep st ts l w

/-- Scalar representation is inhabited, without selecting an encoder. -/
theorem scalar_inhabited {p : PrimTy} (v : p.Denote) (l : Loc) :
    ∃ w : Store, ValueRep (.prim v) .word l w :=
  ⟨fun _ => PrimTy.toWord v, .scalar v l _ rfl⟩

/-- The scalar relation pins the exact full word. -/
theorem scalar_read {p : PrimTy} {v : p.Denote} {l : Loc} {w : Store}
    (h : ValueRep (.prim v) .word l w) : w l = PrimTy.toWord v := by
  cases h with
  | scalar _ _ _ read => exact read

/-- info: 'Solidity.Storage.Representation.scalar_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms scalar_inhabited
/-- info: 'Solidity.Storage.Representation.scalar_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms scalar_read

end Solidity.Storage.Representation
