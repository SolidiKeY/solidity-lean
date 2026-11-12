import Solidity.Yul.World.ReturndataBuiltin
import Solidity.Yul.World.AdapterChecks
namespace Solidity.Yul.World.ReturndataBuiltinControls
open Solidity.Source Solidity.Source.StateExamples
open Solidity.Roadmap (Word)
open Solidity.Yul.World.Checks Solidity.Yul.World.AdapterChecks
open Solidity.Backend.Environment (readMemory)

def oldObserved : ObservedEffects D₀ LW LW :=
  {observed with effects := {observed.effects with returndata := [0xa1,0xb2,0xc3]}}
/-- Explicit frame-outcome fixture, not a reachable-callee certificate. -/
def latest := finishObserved oldObserved parent ⟨[],[],.revert [0xde,0xad,0,0xff]⟩
def before := AdapterRules.Configuration.mk latest memory
def args : Fin 3 → Word := fun i => (#v[toWord 31,toWord 1,toWord 2]).get i
def zeroEnd : Fin 3 → Word := fun i => (#v[toWord 31,toWord 4,toWord 0]).get i
def zeroOutside : Fin 3 → Word := fun i => (#v[toWord 31,toWord 5,toWord 0]).get i
def destinationOutside : Fin 3 → Word := fun i => (#v[⟨2^256-1,by decide⟩,toWord 1,toWord 2]).get i

theorem latest_size : returndataBuiltin .returndatasize TargetMemory.port before (fun i => Fin.elim0 i) =
    some (#v[toWord 4],before) := returndatasize_binding _ _ _
theorem full_readback_and_neighbors : (returndataBuiltin .returndatacopy TargetMemory.port before args).map (fun out =>
    (out.2.observed.effects.returndata,readMemory out.2.memory 30 4)) =
      some ([0xde,0xad,0,0xff],[255,0xad,0,255]) := by
  decide
theorem exact_end_zero : returndataBuiltin .returndatacopy TargetMemory.port before zeroEnd = some (#v[],before) := by
  rfl
theorem out_of_source_zero : returndataBuiltin .returndatacopy TargetMemory.port before zeroOutside = none :=
  returndatacopy_out_of_bounds _ _ _ (by decide)
theorem destination_refusal : returndataBuiltin .returndatacopy TargetMemory.port before destinationOutside = none := by
  rfl
theorem stale_buffer_refused : (returndataBuiltin .returndatacopy TargetMemory.port before args).map
    (fun out => readMemory out.2.memory 31 2) ≠ some [0xb2,0xc3] := by
  decide
end Solidity.Yul.World.ReturndataBuiltinControls
