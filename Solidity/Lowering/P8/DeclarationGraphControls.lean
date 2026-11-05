import Solidity.Lowering.P8.DeclarationGraphCheck
import Solidity.Lowering.V07.LocationProducerControls

/-! Kernel controls for H24 computed certificates and H15 boundaries.
Graph success is distinct from Source refusal and concrete admission.
-/
namespace Solidity.Lowering.P8.DeclarationGraphControls

theorem mixed_views : (Solidity.Lowering.P8.DeclarationGraphCheck.checkOrigin "h24" Solidity.Lowering.V07.LocationProducerControls.mixed).isSome = true := by
  rfl

/-- info: 'Solidity.Lowering.P8.DeclarationGraphControls.mixed_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_views

theorem mapping_memory_policy : ¬ Solidity.Lowering.V07.LocationGraphInterface.StructAdmissible Solidity.Lowering.V07.LocationGraphLaws.E Solidity.Lowering.V07.LocationGraphLaws.loop .memory := by
  decide

/-- info: 'Solidity.Lowering.P8.DeclarationGraphControls.mapping_memory_policy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapping_memory_policy

theorem mapping_calldata_policy : ¬ Solidity.Lowering.V07.LocationGraphInterface.StructAdmissible Solidity.Lowering.V07.LocationGraphLaws.E Solidity.Lowering.V07.LocationGraphLaws.loop .calldata := by
  decide

/-- info: 'Solidity.Lowering.P8.DeclarationGraphControls.mapping_calldata_policy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapping_calldata_policy

theorem graph_without_source_refusal : (Solidity.Lowering.P8.DeclarationGraphCheck.checkOrigin "h24" Solidity.Lowering.V07.LocationGraphLaws.E).isSome = true ∧ ¬ Solidity.Lowering.V07.LocationGraphInterface.SourceRefusesNonAdmissible Solidity.Lowering.V07.LocationGraphLaws.E := by
  exact ⟨by decide, Solidity.Lowering.V07.LocationGraphLaws.refusal_missing⟩

/-- info: 'Solidity.Lowering.P8.DeclarationGraphControls.graph_without_source_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms graph_without_source_refusal

theorem inline_cycle_refused : (Solidity.Lowering.P8.DeclarationGraphCheck.checkOrigin "h24" Solidity.Lowering.V07.GraphAdmissionBoundary.directEnv).isNone = true := by
  rfl

/-- info: 'Solidity.Lowering.P8.DeclarationGraphControls.inline_cycle_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inline_cycle_refused

theorem direct_mapping_memory_refused : ∀ (E : Solidity.Source.Env) (scope : Option String) (key : Solidity.Source.MapKey) (keyName valueName : Option String) (value : Solidity.Source.Syn .typeName), (Solidity.Source.Syn.mapping key keyName value valueName).tys E scope .memory = none := by
  intro E scope key keyName valueName value
  exact Solidity.Lowering.V07.LocationGraphLaws.direct_mapping_refused E scope .memory (by decide) key keyName valueName value

/-- info: 'Solidity.Lowering.P8.DeclarationGraphControls.direct_mapping_memory_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms direct_mapping_memory_refused

theorem direct_mapping_calldata_refused : ∀ (E : Solidity.Source.Env) (scope : Option String) (key : Solidity.Source.MapKey) (keyName valueName : Option String) (value : Solidity.Source.Syn .typeName), (Solidity.Source.Syn.mapping key keyName value valueName).tys E scope .calldata = none := by
  intro E scope key keyName valueName value
  exact Solidity.Lowering.V07.LocationGraphLaws.direct_mapping_refused E scope .calldata (by decide) key keyName valueName value

/-- info: 'Solidity.Lowering.P8.DeclarationGraphControls.direct_mapping_calldata_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms direct_mapping_calldata_refused

theorem mixed_view_counts : (Solidity.Lowering.P8.DeclarationGraphCheck.checkOrigin "h24" Solidity.Lowering.V07.LocationProducerControls.mixed).map (fun g => (g.storage.1, g.memory.1, g.calldata.1)) = some (2,1,1) := by
  rfl

/-- info: 'Solidity.Lowering.P8.DeclarationGraphControls.mixed_view_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_view_counts

end Solidity.Lowering.P8.DeclarationGraphControls
