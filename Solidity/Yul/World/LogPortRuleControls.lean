import Solidity.Yul.World.LogPortRules
import Solidity.Yul.World.LogBuiltinControls
namespace Solidity.Yul.World.LogPortRuleControls
open Solidity.Source Solidity.Source.StateExamples
open Solidity.Roadmap (Word)
open Solidity.Yul.World.Checks Solidity.Yul.World.AdapterChecks
open Solidity.Yul.World.LogBuiltinControls
open Solidity.Yul.World.AdapterRules

def before := Configuration.mk observed memory
def after := Configuration.mk (emitObserved observed log4) memory
theorem actual_log4_continuation : LogStep TargetMemory.port false parent.this ⟨4,by decide⟩
    #v[high,toWord 34,toWord 51,toWord 68] (toWord 7) (toWord 3) before after := by
  exact log_loaded_continuation _ _ _ _ _ _ _ _ _ rfl input_loaded

theorem complete_log4_box : Box (LogStep TargetMemory.port false parent.this ⟨4,by decide⟩
    #v[high,toWord 34,toWord 51,toWord 68] (toWord 7) (toWord 3))
    (fun next => next.observed = emitObserved observed log4 ∧ next.memory = memory) before := by
  exact log_loaded_box _ _ _ _ _ _ _ _ _ rfl input_loaded

theorem missing_has_no_normal_step : Box (LogStep missing false parent.this ⟨4,by decide⟩
    #v[high,toWord 34,toWord 51,toWord 68] (toWord 7) (toWord 3)) (fun _ => False) before := by
  exact log_missing_box _ _ _ _ _ _ _ _ rfl

def wrongLog : Log := ⟨parent.this,⟨4,by decide⟩,#v[toWord 68,toWord 51,toWord 34,high],[17,34,51]⟩
theorem wrong_topics_refused : ¬ LogStep TargetMemory.port false parent.this ⟨4,by decide⟩
    #v[toWord 68,toWord 51,toWord 34,high] (toWord 7) (toWord 3) before after := by
  intro executed
  have complete := log_loaded_box TargetMemory.port before false parent.this ⟨4,by decide⟩
    #v[toWord 68,toWord 51,toWord 34,high] (toWord 7) (toWord 3) [17,34,51] rfl input_loaded
    after executed
  have trace := congrArg (fun out : ObservedEffects D₀ LW LW => out.trace) complete.1
  have different : (emitObserved observed log4).trace ≠ (emitObserved observed wrongLog).trace := by decide
  exact different trace
end Solidity.Yul.World.LogPortRuleControls
