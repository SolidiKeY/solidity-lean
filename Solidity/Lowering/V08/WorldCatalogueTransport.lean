import Solidity.Lowering.V08.WorldCatalogue

/-! Initial-image correctness from installed-code/store and role witnesses.
This builds an existing intrinsic World; it proves no body/execution lowering,
SourceSpec admission, canonical ledger model or bytecode adequacy. -/
namespace Solidity.Lowering.V08.WorldCatalogue
open Solidity
variable {E : Source.Env} {K : Type} {contracts : K → Contract}
  {g : Source.Glob E} {kindOf : String → Option K} {relation : WorldImage.StoreRelation E contracts}
  {source : Source.St E}
theorem assembled_account (inputs : Inputs g kindOf relation source) (environment : Roadmap.SessionEnv)
    (history : List Roadmap.Event) (timestamp : Semantics.Word) (address : ContractWorld.Address) :
    WorldImage.AccountImage g kindOf relation source (assemble inputs environment history timestamp) address := by
  unfold WorldImage.AccountImage
  dsimp only
  split
  · rename_i absent
    simp only [assemble]
    split
    · rfl
    · rename_i index present
      cases absent.symm.trans present
  · rename_i index present
    let entry := inputs.installed (EnvironmentProjection.lowerAddress address) index present
    refine ⟨entry.name, entry.kind, entry.store, entry.selected, entry.linked, ?_, entry.represented⟩
    simp only [assemble]
    split
    · rename_i absent
      cases absent.symm.trans present
    · rename_i other selected
      have same : other = index := Option.some.inj (selected.symm.trans present)
      subst other
      rfl

theorem assembled_image (inputs : Inputs g kindOf relation source) (environment : Roadmap.SessionEnv)
    (history : List Roadmap.Event) (timestamp : Semantics.Word) :
    WorldImage.Image g kindOf relation environment history source (assemble inputs environment history timestamp) where
  accounts address := assembled_account inputs environment history timestamp address
  funds := rfl
  roles name kind linked := inputs.library_role name kind linked

/-- info: 'Solidity.Lowering.V08.WorldCatalogue.assembled_account' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembled_account
/-- info: 'Solidity.Lowering.V08.WorldCatalogue.assembled_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembled_image
end Solidity.Lowering.V08.WorldCatalogue
