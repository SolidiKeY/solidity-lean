import Solidity.Yul.Views.FixedDeclarationTypingControls

namespace Solidity.Yul.Views

/-- Ordinary mutable roots of ONE scope and bank, in actual Env.decls order.
This is not inherited/global root assignment: linearization and origin remain
explicit integration obligations. Constants/immutables do not own such slots. -/
def plainStateVariable (d : Source.Decl) : Bool :=
  match d.kind,d.top,d.node with
  | .stateVar,_,.stateVar _ _ none _ _ _ _ => true
  | _,_,_ => false

def ordinaryRootName? (scope : Option String) (transient : Bool) (d : Source.Decl) : Option Source.DeclName :=
  if d.kind == .stateVar && d.scope == scope && plainStateVariable d && d.isTransient == transient then
    some ⟨d.scope,d.name⟩ else none

def ordinaryRootNames (E : Source.Env) (scope : Option String) (transient : Bool) : List Source.DeclName :=
  E.decls.filterMap (ordinaryRootName? scope transient)

/-- All state-variable IDs, including BOTH banks, constness and malformed nodes. -/
def scopeRootName? (scope : Option String) (d : Source.Decl) : Option Source.DeclName :=
  if d.kind == .stateVar && d.scope == scope then some ⟨d.scope,d.name⟩ else none

def allScopeRootNames (E : Source.Env) (scope : Option String) : List Source.DeclName :=
  E.decls.filterMap (scopeRootName? scope)

/-- Existing typed declaration certificates, indexed by the selected root names
and declared types. Actual rootTy agreement is CHECKED by pack below. -/
inductive RootDeclarations (E : Source.Env) : List (Source.DeclName × Source.STy) → Type where
  | nil : RootDeclarations E []
  | cons {root τ rest} (head : FixedDeclaration E τ) (tail : RootDeclarations E rest) :
      RootDeclarations E ((root,τ)::rest)

abbrev RootPackFn (E : Source.Env) := (a : Roadmap.Address) → Nat →
  Except DeclarationPackingError (List (ScalarPath E.layout (E.lay a)) × Nat)

def RootDeclarations.pack {E ds} (d : RootDeclarations E ds) : RootPackFn E :=
  RootDeclarations.casesOn (motive := fun _ _ => RootPackFn E) d
    (fun _ cursor => .ok ([],cursor))
    (fun {root τ _} head tail a cursor =>
      if E.rootTy root = some τ then
        (head.pack ⟨root,[]⟩ a cursor).bind fun first =>
          (tail.pack a first.2).map fun rest => (first.1++rest.1,rest.2)
      else .error .missingRoot)

/-- Constructor equation keeps simplification local instead of unfolding a
symbolic recursive tail under its eliminator. -/
theorem RootDeclarations.pack_cons {E root τ rest} (head : FixedDeclaration E τ) (tail : RootDeclarations E rest)
    (a : Roadmap.Address) (cursor : Nat) :
    (RootDeclarations.cons (root := root) head tail).pack a cursor =
      if E.rootTy root = some τ then
        (head.pack ⟨root,[]⟩ a cursor).bind (fun first =>
          (tail.pack a first.2).map (fun result => (first.1++result.1,result.2)))
      else .error .missingRoot := rfl

def RootDeclarations.paths {E ds} (d : RootDeclarations E ds) : List Source.SPath :=
  RootDeclarations.casesOn (motive := fun _ _ => List Source.SPath) d []
    (fun {root _ _} head tail => head.paths ⟨root,[]⟩ ++ tail.paths)

def RootDeclarations.endByte {E ds} (d : RootDeclarations E ds) : Nat → Nat :=
  RootDeclarations.casesOn (motive := fun _ _ => Nat → Nat) d id
    (fun head tail cursor => tail.endByte (head.endByte cursor))

inductive RootSequenceError where
  | duplicateDeclarations | duplicateRoots | metadataOrder | packing (reason : DeclarationPackingError)
  deriving DecidableEq, Repr

/-- Actual successful computation and checked inventory; no final layout law
is supplied. Cursor is threaded across roots WITHOUT artificial alignment. -/
structure CheckedRootDeclarations {E ds} (d : RootDeclarations E ds) (scope : Option String)
    (transient : Bool) (a : Roadmap.Address) (origin : Roadmap.Word) where
  ordered : ds.map Prod.fst = ordinaryRootNames E scope transient
  sourceDistinct : (allScopeRootNames E scope).Nodup
  distinct : (ds.map Prod.fst).Nodup
  registrations : List (ScalarPath E.layout (E.lay a))
  endByte : Nat
  packed : d.pack a (origin.val*32) = .ok (registrations,endByte)

def prepareRootDeclarations {E ds} (d : RootDeclarations E ds) (scope : Option String)
    (transient : Bool) (a : Roadmap.Address) (origin : Roadmap.Word) :
    Except RootSequenceError (CheckedRootDeclarations d scope transient a origin) :=
  if sourceDistinct : (allScopeRootNames E scope).Nodup then
    if distinct : (ds.map Prod.fst).Nodup then
      if ordered : ds.map Prod.fst = ordinaryRootNames E scope transient then
        match packed : d.pack a (origin.val*32) with
        | .error reason => .error (.packing reason)
        | .ok (cs,stop) => .ok ⟨ordered,sourceDistinct,distinct,cs,stop,packed⟩
      else .error .metadataOrder
    else .error .duplicateRoots
  else .error .duplicateDeclarations

end Solidity.Yul.Views
