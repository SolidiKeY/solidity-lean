import Solidity.Yul.Views.SourceGraphEndpoints
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Regression controls for the production Source graph slot endpoint bridge.
The joint declaration witness and wrong-root refusal retain their original
statements; neither establishes value adequacy or a reached-state bridge. -/
namespace Solidity.Yul.Views
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
