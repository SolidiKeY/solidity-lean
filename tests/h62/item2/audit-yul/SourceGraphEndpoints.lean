import Solidity.Yul.Views.NestedMappingLayout
import Solidity.Backend.StorageOps.CopyDemandControls
import Solidity.Backend.StorageOps.ProducerInterface

/-! Regression boundary: checked ordinary Source word-mapping declarations
and paths must reach the same symbolic slot as the public typed graph path.
This audit instantiates the existing endpoint interface; it supplies neither
Source value adequacy nor selected-code provenance nor a reached-state bridge. -/
namespace Solidity.Yul.Views

/-- Typed graph image of the existing recursive word-key layout. This adapter
uses the public graph constructors, without introducing a second path syntax. -/
def nestedMappingGraphType (n : Nat) : Nat → TypeGraph.Ty n
  | 0 => .prim .uint
  | depth+1 => .mapping .uint (nestedMappingGraphType n depth)

def nestedMappingGraphKey (key : Roadmap.Word) : PrimTy.uint.Denote :=
  ⟨(key.val : Int), by
    simp only [PrimTy.inRange,decide_eq_true_eq]
    have bound := key.isLt
    omega⟩

theorem nestedMappingGraphKey_word (key : Roadmap.Word) :
    Storage.Representation.keyWord (nestedMappingGraphKey key)=key.val := by rfl

def nestedMappingGraphPath {n : Nat} (G : TypeGraph.Schema n) :
    (keys : List Roadmap.Word) → TypeGraph.Path G
      (nestedMappingGraphType n keys.length) (.prim .uint)
  | [] => .nil
  | key::keys => .cons (.key (nestedMappingGraphKey key)) (nestedMappingGraphPath G keys)

theorem nestedMappingGraphPath_location {n : Nat} (G : TypeGraph.Schema n)
    (keys : List Roadmap.Word) (base : Storage.Loc) :
    Storage.Representation.Graph.pathLoc (nestedMappingGraphPath G keys) base=
      nestedMappingLocation base keys := by
  induction keys generalizing base with
  | nil => rfl
  | cons key keys ih =>
    exact ih (.hash key.val base 0)

theorem nestedMappingGraphPath_supported {n : Nat} (G : TypeGraph.Schema n)
    (keys : List Roadmap.Word) :
    Storage.Representation.Graph.PathSupported (nestedMappingGraphPath G keys) := by
  induction keys with
  | nil => trivial
  | cons key keys ih => exact ⟨True.intro,ih⟩

/-- Checked ordinary Source declaration/path metadata yields the public typed
path endpoint at its existing root0 placement. Slot identity is derived, not
assumed. This does not assert Source liveness, value representation, compiler
selection, numeric-store transport or an actual reached execution. -/
theorem NestedWordMappingRoot.graph_path_endpoint {E root}
    (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : mapping.Keys) {n : Nat} (G : TypeGraph.Schema n) :
    ∃ slot : Evm.Slot,
      Backend.StorageOps.ProducerInterface.PathEndpoint (nestedMappingGraphPath G keys.val)
        (.root 0) slot ∧
      Storage.ofSlot slot=(mapping.entry fixed keys).location := by
  let path := nestedMappingGraphPath G keys.val
  have fits : Backend.StorageOps.TargetOperations.KeysFit (.root 0) := True.intro
  refine ⟨Backend.StorageOps.TargetOperations.toSlot
    (Storage.Representation.Graph.pathLoc path (.root 0))
    (Backend.StorageOps.TargetOperations.path_keysFit path (.root 0) fits),?_,?_⟩
  · exact ⟨nestedMappingGraphPath_supported G keys.val,fits,rfl⟩
  · rw [Backend.StorageOps.TargetOperations.ofSlot_toSlot]
    exact nestedMappingGraphPath_location G keys.val (.root 0)


namespace SourceGraphEndpointAudit
abbrev graph := Backend.StorageOps.CopyDemandControls.graph

/-- Joint declaration witness constructs the ordinary Source metadata through
its existing intrinsic syntax. It does not rely on an execution fixture or
count value adequacy, selected-code provenance or a reached-state bridge. -/
theorem source_path_joint (fixed : Roadmap.Evm.Fixed) :
    ∃ (E : Source.Env) (root : Source.DeclName) (mapping : NestedWordMappingRoot E root)
      (keys : mapping.Keys) (slot : Evm.Slot),
      mapping.depth=2 ∧
      (mapping.entry fixed keys).path.steps=
        [.key (Source.wordBytes 1),.key (Source.wordBytes 2)] ∧
      Backend.StorageOps.ProducerInterface.PathEndpoint
        (nestedMappingGraphPath graph keys.val) (.root 0) slot ∧
      Storage.ofSlot slot=(mapping.entry fixed keys).location := by
  let uint : Source.Syn .typeName := .elem (.int false 256 (by decide))
  let key : Source.MapKey := .elem (.int false 256 (by decide)) (by decide)
  let ty : Source.Syn .typeName := .mapping key none (.mapping key none uint none) none
  let E : Source.Env := ⟨[
    ⟨.stateVar,"table",none,true,.stateVar ty none none none false "table" .none⟩]⟩
  let root : Source.DeclName := ⟨none,"table"⟩
  let mapping : NestedWordMappingRoot E root := ⟨2,by decide,rfl,rfl⟩
  let keys : mapping.Keys := ⟨[1,2],rfl⟩
  obtain ⟨slot,endpoint,image⟩ := mapping.graph_path_endpoint fixed keys graph
  exact ⟨E,root,mapping,keys,slot,rfl,rfl,endpoint,image⟩

/-- Regression refusal: a nonempty two-key path cannot be certified as the
untouched root slot. This is symbolic identity, without hash injectivity. -/
theorem wrong_root_refused :
    ¬ Backend.StorageOps.ProducerInterface.PathEndpoint
      (nestedMappingGraphPath graph ([1,2] : List Roadmap.Word)) (.root 0) (.root 0) := by
  intro endpoint
  have same := congrArg Storage.ofSlot endpoint.image
  rw [Backend.StorageOps.TargetOperations.ofSlot_toSlot] at same
  change Storage.Loc.root 0=Storage.Loc.hash 2 (.hash 1 (.root 0) 0) 0 at same
  cases same
end SourceGraphEndpointAudit

end Solidity.Yul.Views
