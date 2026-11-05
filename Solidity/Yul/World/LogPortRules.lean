import Solidity.Yul.World.AdapterRules
/-! Constructive rules for existing normal-return port relations (Lean-only).
Actual load facts derive both a continuation and a full-state box; no desired
LogStep equation is a premise. These are not intrinsic Yul/G51 or Source/G01
adequacy rules, and normal-refusal laws do not classify exceptional EVM halts. -/
namespace Solidity.Yul.World.AdapterRules
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
variable {D : Layout} {L T : Address → SPath → STy} {Memory : Type}
theorem log_loaded_continuation (port : BytePort Memory) (before : Configuration Memory D L T)
    (static : Bool) (emitter : Address) (count : Fin 5)
    (topics : Vector Word count.val) (offset size : Word) (bytes : Bytes)
    (normal : static = false) (loaded : port.load before.memory offset size = some bytes) :
    LogStep port static emitter count topics offset size before
      ⟨emitObserved before.observed ⟨emitter,count,topics,bytes⟩,before.memory⟩ := by
  subst static
  exact ⟨logAdapter_exact port before.observed before.memory emitter count topics offset size bytes loaded,rfl⟩
theorem log_loaded_box (port : BytePort Memory) (before : Configuration Memory D L T)
    (static : Bool) (emitter : Address) (count : Fin 5)
    (topics : Vector Word count.val) (offset size : Word) (bytes : Bytes)
    (normal : static = false) (loaded : port.load before.memory offset size = some bytes) :
    Box (LogStep port static emitter count topics offset size)
      (fun after => after.observed = emitObserved before.observed ⟨emitter,count,topics,bytes⟩ ∧
        after.memory = before.memory) before := by
  subst static
  exact log_step_eq port emitter count topics offset size before
    (emitObserved before.observed ⟨emitter,count,topics,bytes⟩)
    (logAdapter_exact port before.observed before.memory emitter count topics offset size bytes loaded)
theorem log_missing_box (port : BytePort Memory) (before : Configuration Memory D L T)
    (static : Bool) (emitter : Address) (count : Fin 5)
    (topics : Vector Word count.val) (offset size : Word)
    (missing : port.load before.memory offset size = none) :
    Box (LogStep port static emitter count topics offset size) (fun _ => False) before := by
  intro after step
  have completed := step.1
  cases static <;> simp only [logAdapter, Bool.false_eq_true, ↓reduceIte, missing,
    bind, Option.bind_none] at completed <;> cases completed
end Solidity.Yul.World.AdapterRules
