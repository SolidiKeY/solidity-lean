import Solidity.Yul.World.TargetCallRules
import Solidity.Yul.World.AdapterChecks

/-! Scripted nonvacuity and guard controls. No source reachability claim. -/
namespace Solidity.Yul.World.TargetCallRuleChecks
open Solidity.Source
open Solidity.Source.StateExamples
open Solidity.Yul.World.Checks
open Solidity.Yul.World.AdapterChecks
open Solidity.Backend.Environment (Memory readMemory writeBytes)

def before : AdapterRules.Configuration Memory D₀ LW LW := ⟨observed, memory⟩
def after (fail : Bool) : AdapterRules.Configuration Memory D₀ LW LW :=
  ⟨done fail, writeBytes memory 31 (callOutput (returnData (answer fail [17,34,51]).outcome) 2)⟩
theorem normal_inhabited (fail : Bool) :
 AdapterRules.CallStep TargetMemory.port (producer fail) parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
      (answer fail [17,34,51]).outcome before (after fail) := by
  exact ⟨_, TargetMemory.call_output_exact (producer fail) observed memory parent .call (addr 3)
    (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
    [17,34,51] (answer fail [17,34,51]) rfl rfl input_loaded rfl, rfl, rfl, rfl⟩

theorem full_box (fail : Bool) :
 AdapterRules.Box
      (AdapterRules.CallStep TargetMemory.port (producer fail) parent .call (addr 3)
        (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
        (answer fail [17,34,51]).outcome)
      (fun next => next.observed = done fail ∧
        readMemory next.memory 31 (callOutput (returnData (answer fail [17,34,51]).outcome) 2).length =
          callOutput (returnData (answer fail [17,34,51]).outcome) 2 ∧
        ∀ i, (i < 31 ∨ 31 + min 2 (returnData (answer fail [17,34,51]).outcome).length ≤ i) →
          next.memory i = memory i) before := by
  exact TargetMemory.call_output_box (producer fail) before parent .call (addr 3)
    (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
    [17,34,51] (answer fail [17,34,51]) rfl rfl input_loaded rfl

theorem preflight_no_step :
 ∀ next, ¬ AdapterRules.CallStep TargetMemory.port (producer false)
      { parent with static := true } .call (addr 3)
      (toWord 100000) (toWord 1) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
      (.success [17,34,51]) before next := by
  intro next hs
  obtain ⟨result, hr, _, _, _⟩ := hs
  simp only [before] at hr
  rw [static_value_preflight_control] at hr
  cases hr

/-- The universal rule is applied to an inhabited transition for both outcomes. -/
theorem applied (fail : Bool) :
    (after fail).observed = done fail ∧
    readMemory (after fail).memory 31
      (callOutput (returnData (answer fail [17,34,51]).outcome) 2).length =
      callOutput (returnData (answer fail [17,34,51]).outcome) 2 ∧
    ∀ i, (i < 31 ∨ 31 + min 2 (returnData (answer fail [17,34,51]).outcome).length ≤ i) →
      (after fail).memory i = memory i :=
  full_box fail (after fail) (normal_inhabited fail)

#check TargetMemory.call_output_box
#print axioms TargetMemory.call_output_box
#print axioms normal_inhabited
#print axioms full_box
#print axioms preflight_no_step
#print axioms applied
end Solidity.Yul.World.TargetCallRuleChecks
