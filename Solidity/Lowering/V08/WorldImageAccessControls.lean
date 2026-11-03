import Solidity.Lowering.V08.WorldImageAccess
import Solidity.Lowering.V08.WorldCatalogueControls

/-! Concrete clients of typed image lookup. These retain the actual source
persistent/transient relation before/after reset and complete intrinsic stores.
They do not establish body execution, admission, runtime frames or bytecode. -/
namespace Solidity.Lowering.V08.WorldImageAccessControls
open Solidity

def located (pipeline : Roadmap.Pipeline) :
    ∃ store : Storage WorldResetControls.Cell,
      (WorldCatalogueControls.world pipeline).accounts
        (EnvironmentProjection.liftAddress SourceEnvironmentControls.self) = some ⟨(),store⟩ ∧
      WorldResetControls.relation SourceEnvironmentControls.self ()
        (SourceEnvironmentControls.populated.ex.world.accounts SourceEnvironmentControls.self).storage
        (SourceEnvironmentControls.populated.ex.transient.cells SourceEnvironmentControls.self) store :=
  WorldImageAccess.installed_store (WorldCatalogueControls.initial_image pipeline)
    SourceEnvironmentControls.self 0 "C" () rfl rfl rfl

def reset_located (pipeline : Roadmap.Pipeline) :
    ∃ store : Storage WorldResetControls.Cell,
      (WorldCatalogueControls.world pipeline).resetTransient.accounts
        (EnvironmentProjection.liftAddress SourceEnvironmentControls.self) = some ⟨(),store⟩ ∧
      WorldResetControls.relation SourceEnvironmentControls.self ()
        ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.world.accounts SourceEnvironmentControls.self).storage
        ((SourceTransient.endExecution SourceEnvironmentControls.populated).ex.transient.cells SourceEnvironmentControls.self) store :=
  WorldImageAccess.installed_store (WorldCatalogueControls.reset_image pipeline)
    SourceEnvironmentControls.self 0 "C" () rfl rfl rfl

theorem storage_values (pipeline : Roadmap.Pipeline) :
    ((WorldCatalogueControls.world pipeline).storage?
      (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ()),
     (WorldCatalogueControls.world pipeline).resetTransient.storage?
      (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ()),
     (WorldCatalogueControls.world pipeline).storage?
      (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.sender⟩ : ContractWorld.Handle ())) =
    (some (WorldResetControls.store true true), some (WorldResetControls.store true false), none) := by
  rfl

theorem no_sender_alias (pipeline : Roadmap.Pipeline) :
    ((WorldCatalogueControls.world pipeline).storage?
      (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.sender⟩ : ContractWorld.Handle ())).isSome ≠
    ((WorldCatalogueControls.world pipeline).storage?
      (⟨EnvironmentProjection.liftAddress SourceEnvironmentControls.self⟩ : ContractWorld.Handle ())).isSome := by
  change false ≠ true
  decide +kernel

/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.located' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms located
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.reset_located' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reset_located
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.storage_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms storage_values
/-- info: 'Solidity.Lowering.V08.WorldImageAccessControls.no_sender_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_sender_alias
end Solidity.Lowering.V08.WorldImageAccessControls
