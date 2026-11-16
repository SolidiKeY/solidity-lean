import Solidity.Yul.World.CallBuiltin
import Solidity.Yul.World.AdapterChecks
namespace Solidity.Yul.World.CallBuiltinControls
open Solidity.Source Solidity.Source.StateExamples
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.World.Checks Solidity.Yul.World.AdapterChecks
open Solidity.Backend.Environment (Memory readMemory)

def before := AdapterRules.Configuration.mk observed memory
def caller := {parent with this := addr 0x20, caller := addr 0x40, value := toWord 9}
def highTarget : Word := toWord (2^200 + 0x30)
def callArgs : Fin 7 → Word := fun i => (#v[toWord 100000,highTarget,toWord 0,toWord 7,toWord 3,toWord 31,toWord 2]).get i
def shortArgs : Fin 6 → Word := fun i => (#v[toWord 100000,highTarget,toWord 7,toWord 3,toWord 31,toWord 2]).get i
/-- Guarded outcome fixture; no reachable code/world/static adequacy certificate. -/
def contextOK (kind : CallKind) (frame : CallFrame) : Bool :=
  match kind with
  | .call => decide (frame.this = addr 0x30 ∧ frame.caller = addr 0x20 ∧ frame.value = toWord 0 ∧ frame.static = false)
  | .staticcall => decide (frame.this = addr 0x30 ∧ frame.caller = addr 0x20 ∧ frame.value = toWord 0 ∧ frame.static = true)
  | .delegatecall => decide (frame.this = addr 0x20 ∧ frame.caller = addr 0x40 ∧ frame.value = toWord 9 ∧ frame.static = false)
def fixture (fail : Bool) : WorldPort D₀ LW LW := fun _ kind callee gas frame input =>
  if callee = addr 0x30 ∧ gas = toWord 100000 ∧ input = [17,34,51] ∧ contextOK kind frame = true then
    some ⟨[],[],if fail then .revert input else .success input⟩ else none

def summary (result : CompletedCall Memory D₀ LW LW) :=
  (callFlag result.outcome,result.observed.effects.returndata,result.observed.trace,
    result.copiedMemory.map (fun m => readMemory m 31 3),
    (callContinuation result).map (fun out => (out.1.get 0,out.2.observed.effects.returndata)))

theorem call_exact : (callBuiltin .call TargetMemory.port (fixture false) before caller callArgs).map summary =
    some (toWord 1,[17,34,51],callerTrace,some [17,34,255],some (toWord 1,[17,34,51])) := by
  rfl
theorem staticcall_exact : (callBuiltin .staticcall TargetMemory.port (fixture false) before caller shortArgs).map summary =
    some (toWord 1,[17,34,51],callerTrace,some [17,34,255],some (toWord 1,[17,34,51])) := by
  rfl
theorem delegatecall_revert_exact : (callBuiltin .delegatecall TargetMemory.port (fixture true) before caller shortArgs).map summary =
    some (toWord 0,[17,34,51],callerTrace,some [17,34,255],some (toWord 0,[17,34,51])) := by
  rfl

def refuseStore : BytePort Memory := {TargetMemory.port with store := fun _ _ _ => none}
theorem copy_refusal_retains_completion : (callBuiltin .call refuseStore (fixture false) before caller callArgs).map (fun result =>
    (result.outcome,result.observed.effects.returndata,result.copiedMemory.isNone,(callContinuation result).isNone)) =
      some (.success [17,34,51],[17,34,51],true,true) := by
  decide
theorem dirty_target_low_bits : calleeAddress highTarget = addr 0x30 ∧ highTarget.val ≠ 0x30 := by
  decide
def unconditional : WorldPort D₀ LW LW := fun _ _ _ _ _ input => some ⟨[],[],.success input⟩
def nonzeroArgs : Fin 7 → Word := fun i => if i = 2 then toWord 1 else callArgs i
theorem static_value_unconfounded : callBuiltin .call TargetMemory.port unconditional before {caller with static:=true} nonzeroArgs = none ∧
    (callBuiltin .call TargetMemory.port unconditional before caller nonzeroArgs).isSome = true :=
  ⟨callBuiltin_static_value _ _ _ _ _ rfl (by decide),rfl⟩
def wrongInput : Fin 7 → Word := fun i => if i = 3 then toWord 8 else callArgs i
theorem wrong_input_refused : callBuiltin .call TargetMemory.port (fixture false) before caller wrongInput = none := by
  rfl
def staticDelegate : WorldPort D₀ LW LW := fun _ kind callee gas frame input =>
  if kind = .delegatecall ∧ callee = addr 0x30 ∧ gas = toWord 100000 ∧ input = [17,34,51] ∧
      frame.static = true ∧ frame.this = addr 0x20 ∧ frame.caller = addr 0x40 ∧ frame.value = toWord 9 then
    some ⟨[],[],.success input⟩ else none
theorem delegate_parent_static : (callBuiltin .delegatecall TargetMemory.port staticDelegate before {caller with static:=true} shortArgs).map summary =
    some (toWord 1,[17,34,51],callerTrace,some [17,34,255],some (toWord 1,[17,34,51])) := by
  rfl
end Solidity.Yul.World.CallBuiltinControls
