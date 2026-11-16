import Solidity.Yul.World.LogSuccess
import Solidity.Yul.World.LogBuiltinControls
namespace Solidity.Yul.World.LogSuccessControls
open Solidity.Source Solidity.Source.StateExamples
open Solidity.Roadmap (Word)
open Solidity.Yul.World.Checks Solidity.Yul.World.AdapterChecks
open Solidity.Yul.World.LogBuiltinControls

def decorated : ObservedEffects D₀ LW LW :=
  {observed with effects := {observed.effects with returndata := [0xfa,0,0xbc]}}
def emptyArgs : Fin 2 → Word := fun i => (#v[toWord 7,toWord 0]).get i
def emptyLog : Log := ⟨parent.this,⟨0,by decide⟩,#v[],[]⟩

theorem empty_log_emitted : logBuiltin .log0 TargetMemory.port decorated memory parent emptyArgs =
    some (emitObserved decorated emptyLog) := by
  exact log0_binding _ _ _ _ _ _ rfl (by decide)

theorem empty_log_observable : logBuiltin .log0 TargetMemory.port decorated memory parent emptyArgs ≠ some decorated := by
  exact logBuiltin_not_identity _ _ _ _ _ _

theorem full_caller_frame : (emitObserved decorated emptyLog).effects.execution = decorated.effects.execution ∧
    (emitObserved decorated emptyLog).effects.returndata = [0xfa,0,0xbc] ∧
    (emitObserved decorated emptyLog).trace = observed.trace ++ [.log emptyLog] := by
  exact ⟨rfl,rfl,rfl⟩

theorem missing_zero_window : logBuiltin .log0 missing decorated memory parent emptyArgs = none := rfl

theorem static_empty_refused : logBuiltin .log0 TargetMemory.port decorated memory {parent with static:=true} emptyArgs = none := by
  exact logBuiltin_static _ _ _ _ _ _
end Solidity.Yul.World.LogSuccessControls
