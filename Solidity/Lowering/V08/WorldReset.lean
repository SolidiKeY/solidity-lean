import Solidity.Lowering.V08.WorldImage

/-! Relative transaction-boundary reset transport. ResetInputs is an explicit
per-store P7/layout duty. This does not identify raw/reset worlds or reset internal
calls. SourceSpec, layout, admission and compiled-unit adequacy remain open. -/
namespace Solidity.Lowering.V08.WorldImage
open Solidity
variable {E : Source.Env} {K : Type} {contracts : K → Contract}
  {g : Source.Glob E} {kindOf : String → Option K}
  {relation : StoreRelation E contracts}
  {source : Source.St E} {target : ContractWorld.World contracts}

theorem account_reset (slots : ResetInputs relation) (address : ContractWorld.Address)
    (image : AccountImage g kindOf relation source target address) :
    AccountImage g kindOf relation (SourceTransient.endExecution source)
      target.resetTransient address := by
  unfold AccountImage at image ⊢
  cases code : (source.ex.world.accounts (EnvironmentProjection.lowerAddress address)).code with
  | none =>
    simp only [SourceTransient.endExecution, Source.ExecState.endTx, code] at image ⊢
    rw [ContractWorld.World.resetTransient_accounts, image]
    rfl
  | some codeIndex =>
    simp only [SourceTransient.endExecution, Source.ExecState.endTx, code] at image ⊢
    obtain ⟨name, kind, store, selected, linked, installed, represented⟩ := image
    refine ⟨name, kind, Storage.resetTransient store, selected, linked, ?_, ?_⟩
    · rw [ContractWorld.World.resetTransient_accounts, installed]
      rfl
    · exact slots.slots _ _ _ _ _ represented

theorem image_reset {environment : Roadmap.SessionEnv} {history : List Roadmap.Event}
    (slots : ResetInputs relation)
    (image : Image g kindOf relation environment history source target) :
    Image g kindOf relation environment history (SourceTransient.endExecution source)
      target.resetTransient where
  accounts address := account_reset slots address (image.accounts address)
  funds := image.funds
  roles := image.roles

/-- info: 'Solidity.Lowering.V08.WorldImage.account_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms account_reset
/-- info: 'Solidity.Lowering.V08.WorldImage.image_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms image_reset
end Solidity.Lowering.V08.WorldImage
