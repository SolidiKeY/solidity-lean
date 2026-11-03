import Solidity.Yul.Views.RootDeclarationReadback

namespace Solidity.Yul.Views

/-- Actual well-shaped contract/interface declarations, without visibility filtering.
Private base storage belongs to the physical inventory too. -/
def storageContract? (name : String) (d : Source.Decl) : Bool :=
  d.scope == none && d.name == name && match d.kind,d.top,d.node with
  | .contract,_,.contract _ _ _ _ _ => true
  | .interface,_,.interface _ _ _ => true
  | _,_,_ => false

def contractIdentity? (d : Source.Decl) : Option String :=
  if d.scope == none && (d.kind == .contract || d.kind == .interface) then some d.name else none

inductive InheritedLayoutError where
  | duplicateContracts | invalidBases | noLinearization | malformedLineage
  | duplicateDeclarations | duplicateRoots | metadataOrder | packing (reason : DeclarationPackingError)
  deriving DecidableEq, Repr

/-- Results of CHECKING the existing owner computation and actual declaration
metadata. No independent C3 implementation or layout adequacy law. -/
structure StorageHierarchy (E : Source.Env) (active : String) where
  order : List String
  linearized : E.linearize active = some order.reverse
  unique : order.Nodup
  activeHead : order.reverse.head? = some active
  identities : (E.decls.filterMap contractIdentity?).Nodup
  validBases : E.basesOK = true
  declared : ∀ name ∈ order, E.decls.any (storageContract? name) = true
  closed : ∀ name ∈ order, ∀ base ∈ E.bases name, base ∈ order

/-- Reverse MOST-derived-first owner C3, exactly as solc's storage rules require.
Checks catch unknown roots/bases and ambiguous metadata that owner linearize
alone can accept. All iteration is over real declaration/owner outputs. -/
def prepareStorageHierarchy (E : Source.Env) (active : String) :
    Except InheritedLayoutError (StorageHierarchy E active) :=
  if identities : (E.decls.filterMap contractIdentity?).Nodup then
    if validBases : E.basesOK = true then
      match lin : E.linearize active with
      | none => .error .noLinearization
      | some chain =>
        if unique : chain.reverse.Nodup then
          if activeHead : chain.head? = some active then
            if declared : ∀ name ∈ chain.reverse, E.decls.any (storageContract? name) = true then
              if closed : ∀ name ∈ chain.reverse, ∀ base ∈ E.bases name, base ∈ chain.reverse then
                .ok ⟨chain.reverse,by simpa only [List.reverse_reverse] using lin,unique,
                  by simpa only [List.reverse_reverse] using activeHead,identities,validBases,declared,closed⟩
              else .error .malformedLineage
            else .error .malformedLineage
          else .error .malformedLineage
        else .error .malformedLineage
    else .error .invalidBases
  else .error .duplicateContracts

def inheritedRootNames (E : Source.Env) (order : List String) (tr : Bool) : List Source.DeclName :=
  order.flatMap fun name => ordinaryRootNames E (some name) tr

/-- Intrinsic existing RootDeclarations computation over the COMPLETE selected
inherited inventory. Origin remains explicit, NOT evaluated from layout-at. -/
structure CheckedInheritedDeclarations {E ds} (d : RootDeclarations E ds)
    (active : String) (tr : Bool) (a : Roadmap.Address) (origin : Roadmap.Word) where
  hierarchy : StorageHierarchy E active
  ordered : ds.map Prod.fst = inheritedRootNames E hierarchy.order tr
  sourceDistinct : ∀ scope ∈ hierarchy.order, (allScopeRootNames E (some scope)).Nodup
  distinct : (ds.map Prod.fst).Nodup
  registrations : List (ScalarPath E.layout (E.lay a))
  endByte : Nat
  packed : d.pack a (origin.val*32) = .ok (registrations,endByte)

def prepareInheritedDeclarations {E ds} (d : RootDeclarations E ds) (active : String)
    (tr : Bool) (a : Roadmap.Address) (origin : Roadmap.Word) :
    Except InheritedLayoutError (CheckedInheritedDeclarations d active tr a origin) := do
  let h ← prepareStorageHierarchy E active
  if sourceDistinct : ∀ scope ∈ h.order, (allScopeRootNames E (some scope)).Nodup then
    if distinct : (ds.map Prod.fst).Nodup then
      if ordered : ds.map Prod.fst = inheritedRootNames E h.order tr then
        match packed : d.pack a (origin.val*32) with
        | .error reason => .error (.packing reason)
        | .ok (cs,stop) => .ok ⟨h,ordered,sourceDistinct,distinct,cs,stop,packed⟩
      else .error .metadataOrder
    else .error .duplicateRoots
  else .error .duplicateDeclarations

end Solidity.Yul.Views
