import Solidity.Yul.World.LogBuiltin
import Solidity.Yul.World.AdapterChecks

/-! Intrinsic LOG controls: full-width topics, exact order, delegated emitter,
static refusal, missing bytes and failed-frame rollback. No callee certificate. -/
namespace Solidity.Yul.World.LogBuiltinControls
open Solidity.Source
open Solidity.Source.StateExamples
open Solidity.Roadmap (Word)
open Solidity.Yul.World.Checks
open Solidity.Yul.World.AdapterChecks
open Solidity.Backend.Environment (Memory)

def high : Word := ⟨2^255+17,by decide⟩
def args0 : Fin 2 → Word := fun i => (#v[toWord 7,toWord 3]).get i
def args1 : Fin 3 → Word := fun i => (#v[toWord 7,toWord 3,high]).get i
def args2 : Fin 4 → Word := fun i => (#v[toWord 7,toWord 3,high,toWord 34]).get i
def args3 : Fin 5 → Word := fun i => (#v[toWord 7,toWord 3,high,toWord 34,toWord 51]).get i
def args4 : Fin 6 → Word := fun i => (#v[toWord 7,toWord 3,high,toWord 34,toWord 51,toWord 68]).get i

theorem log0_exact : logBuiltin .log0 TargetMemory.port observed memory parent args0 =
    some (emitObserved observed ⟨parent.this,⟨0,by decide⟩,#v[],[17,34,51]⟩) :=
  log0_binding _ _ _ _ _ _ rfl input_loaded

theorem log1_exact : logBuiltin .log1 TargetMemory.port observed memory parent args1 =
    some (emitObserved observed ⟨parent.this,⟨1,by decide⟩,#v[high],[17,34,51]⟩) :=
  log1_binding _ _ _ _ _ _ rfl input_loaded

theorem log2_exact : logBuiltin .log2 TargetMemory.port observed memory parent args2 =
    some (emitObserved observed ⟨parent.this,⟨2,by decide⟩,#v[high,toWord 34],[17,34,51]⟩) :=
  log2_binding _ _ _ _ _ _ rfl input_loaded

theorem log3_exact : logBuiltin .log3 TargetMemory.port observed memory parent args3 =
    some (emitObserved observed ⟨parent.this,⟨3,by decide⟩,#v[high,toWord 34,toWord 51],[17,34,51]⟩) :=
  log3_binding _ _ _ _ _ _ rfl input_loaded

def log4 : Log := ⟨parent.this,⟨4,by decide⟩,#v[high,toWord 34,toWord 51,toWord 68],[17,34,51]⟩
theorem log4_exact : logBuiltin .log4 TargetMemory.port observed memory parent args4 =
    some (emitObserved observed log4) := log4_binding _ _ _ _ _ _ rfl input_loaded

theorem delegated_emitter :
    logBuiltin .log4 TargetMemory.port observed memory
      (childContext observed.effects.execution parent .delegatecall (addr 3) (toWord 99) [9]) args4 =
    some (emitObserved observed log4) := log4_binding _ _ _ _ _ _ rfl input_loaded

theorem static_refusal :
    logBuiltin .log4 TargetMemory.port observed memory {parent with static:=true} args4 = none :=
  logBuiltin_static _ _ _ _ _ _

def missing : BytePort Memory := {TargetMemory.port with load:=fun _ _ _ => none}
theorem missing_refusal : logBuiltin .log4 missing observed memory parent args4 = none := by
  rfl

theorem failed_frame :
    (finishObserved observed parent ⟨havoc,calleeTrace ++ [.log log4],.revert [253]⟩).effects =
      ⟨fundedPrefix,observed.effects.logs,[253]⟩ ∧
    (finishObserved observed parent ⟨havoc,calleeTrace ++ [.log log4],.revert [253]⟩).trace =
      rollbackTrace observed.trace calleeTrace := finishObserved_logged_revert _ _ _ _ _ _
theorem topic_order_negative : log4.topics ≠ #v[toWord 68,toWord 51,toWord 34,high] := by
  decide

theorem high_topic_retained : (log4.topics.get ⟨0,by decide⟩).val = 2^255+17 := by
  rfl

end Solidity.Yul.World.LogBuiltinControls
