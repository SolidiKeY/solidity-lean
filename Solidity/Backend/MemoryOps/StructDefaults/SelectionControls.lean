import Solidity.Backend.MemoryOps.StructDefaults.NestedWordControls

/-! Concrete selector controls for the finite layouts used by the inhabited
Source/intrinsic/word examples. These identify the hand-built plans with the
actual selector results; they do not claim source/word address agreement. -/
namespace Solidity.Backend.MemoryOps.StructDefaults.SelectionControls
open Evm Evm.Memory

theorem pair_selected : defaultPlan? (.struct WordControls.pairName) =
    some WordControls.plan := by rfl

theorem nested_selected : defaultPlan? (.struct NestedWordControls.nestedName) =
    some NestedWordControls.nestedPlan := by rfl

/-- Inspect the allocated parent, including both of its typed fields. -/
theorem parent_observed :
    ∃ fs : Source.DataList Controls.E.layout (Controls.E.layout.fields Controls.name),
      Controls.completed.2.heap.get 2 =
        some ⟨.struct .memory Controls.name, Source.Data.struct fs⟩ ∧
      fs.nth 0 (.int .u256) = .ok (.val (.int 0 Source.IntTy.u256.zero_mem)) ∧
      fs.nth 1 SourceBoolArrayTy = .ok (.val (.memRef rfl 1)) := by
  obtain ⟨fs, evaluated, tag, child⟩ := Controls.constructed
  refine ⟨fs, ?_, tag, child⟩
  unfold Controls.completed
  rw [evaluated]
  exact pairHeap_parent Controls.initial.heap Controls.name fs

/-- One less than the nested construction's required fuel really times out
before any allocation; no successful observation is substituted. -/
theorem nested_fuel_eight :
    (Source.zeroVal (E := Controls.E) (Γ := []) 8
      (.struct .memory Controls.outerName)).run Controls.state =
        (.error .timeout, Controls.state) := by rfl

/-- The observed word execution is the code actually selected for Pair. -/
theorem selected_pair_observation :
    (defaultPlan? (.struct WordControls.pairName)).map
      (fun plan => WordControls.observe (run plan.code WordControls.machine)) =
        some (some [129,77,131,99,0,0,128]) := by
  rw [pair_selected]
  exact congrArg some WordControls.target_observation

/-- The nested execution likewise uses the selected finite default layout. -/
theorem selected_nested_observation :
    (defaultPlan? (.struct NestedWordControls.nestedName)).map
      (fun plan => NestedWordControls.observe (run plan.code WordControls.machine)) =
        some (some [131,77,133,99,0,0,128,129,0]) := by
  rw [nested_selected]
  exact congrArg some NestedWordControls.target_observation

#print axioms pair_selected
#print axioms nested_selected
#print axioms parent_observed
#print axioms nested_fuel_eight
#print axioms selected_pair_observation
#print axioms selected_nested_observation
end Solidity.Backend.MemoryOps.StructDefaults.SelectionControls
