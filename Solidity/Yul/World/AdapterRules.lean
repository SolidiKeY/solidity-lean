import Solidity.Yul.World.Adapters

/-! # Equation-indexed port determinism (Lean-only)
These judgments are indexed by existing typed effects and producer memory.
They are not a replacement Yul AST, source embedding or G51/dl adequacy theorem.
The normal-return relations preserve the distinction from preflight/copy faults.
`*_step_eq` takes the same adapter equation defining Step. These are
determinism laws, not independent Yul/Source calculus or port adequacy.
-/
namespace Solidity.Yul.World.AdapterRules
open Solidity.Source
open Solidity.Roadmap (Address Word Outcome)
variable {D : Layout} {L T : Address → SPath → STy} {Memory : Type}

structure Configuration (Memory : Type) (D : Layout) (L T : Address → SPath → STy) where
  observed : ObservedEffects D L T
  memory : Memory

def CallStep (port : BytePort Memory) (invoke : WorldPort D L T) (parent : CallFrame)
    (kind : CallKind) (callee : Address) (gas value inputOffset inputSize outputOffset outputSize : Word)
    (outcome : Outcome) (before after : Configuration Memory D L T) : Prop :=
  ∃ result, callAdapter port invoke before.observed before.memory parent kind callee gas value
      inputOffset inputSize outputOffset outputSize = some result ∧
    result.outcome = outcome ∧ result.copiedMemory = some after.memory ∧ after.observed = result.observed

def CopyStep (port : BytePort Memory) (destination source size : Word)
    (before after : Configuration Memory D L T) : Prop :=
  copyReturndata port before.observed.effects before.memory destination source size = some after.memory ∧
    after.observed = before.observed

def LogStep (port : BytePort Memory) (static : Bool) (emitter : Address)
    (count : Fin 5) (topics : Vector Word count.val) (offset size : Word)
    (before after : Configuration Memory D L T) : Prop :=
  logAdapter port before.observed before.memory static emitter count topics offset size = some after.observed ∧
    after.memory = before.memory

/-- Semantic box for these concrete normal-return relations only. -/
def Box (step : Configuration Memory D L T → Configuration Memory D L T → Prop)
    (post : Configuration Memory D L T → Prop) (before : Configuration Memory D L T) : Prop :=
  ∀ after, step before after → post after

/-- Exact copy postcondition proved from the actual copy function equality. -/
theorem copy_step_eq (port : BytePort Memory) (destination source size : Word)
    (before : Configuration Memory D L T) (memory : Memory)
    (h : copyReturndata port before.observed.effects before.memory destination source size = some memory) :
    Box (CopyStep port destination source size)
      (fun after => after.observed = before.observed ∧ after.memory = memory) before := by
  intro after hs
  refine ⟨hs.2, ?_⟩
  have hh := hs.1
  rw [h] at hh
  exact (Option.some.inj hh).symm

/-- Exact call postcondition, preserving outcome/trace carried by the actual
completed invocation; physical refusal is not a normal CallStep. -/
theorem call_step_eq (port : BytePort Memory) (invoke : WorldPort D L T) (parent : CallFrame)
    (kind : CallKind) (callee : Address) (gas value inputOffset inputSize outputOffset outputSize : Word)
    (before : Configuration Memory D L T) (result : CompletedCall Memory D L T)
    (memory : Memory)
    (h : callAdapter port invoke before.observed before.memory parent kind callee gas value
      inputOffset inputSize outputOffset outputSize = some result)
    (hc : result.copiedMemory = some memory) :
    Box (CallStep port invoke parent kind callee gas value inputOffset inputSize outputOffset outputSize result.outcome)
      (fun after => after.observed = result.observed ∧ after.memory = memory) before := by
  intro after hs
  obtain ⟨r, hr, _, hm, he⟩ := hs
  rw [h] at hr
  cases Option.some.inj hr
  refine ⟨he, ?_⟩
  rw [hc] at hm
  exact (Option.some.inj hm).symm

theorem log_step_eq (port : BytePort Memory) (emitter : Address)
    (count : Fin 5) (topics : Vector Word count.val) (offset size : Word)
    (before : Configuration Memory D L T) (observed : ObservedEffects D L T)
    (h : logAdapter port before.observed before.memory false emitter count topics offset size = some observed) :
    Box (LogStep port false emitter count topics offset size)
      (fun after => after.observed = observed ∧ after.memory = before.memory) before := by
  intro after hs
  refine ⟨?_, hs.2⟩
  have hh := hs.1
  rw [h] at hh
  exact (Option.some.inj hh).symm

/-- Static logging has no normal continuation. This does not replace the
caller exceptional-halt/rollback transition required by final source embedding. -/
theorem static_log_rule (port : BytePort Memory) (emitter : Address)
    (count : Fin 5) (topics : Vector Word count.val) (offset size : Word)
    (before : Configuration Memory D L T) :
    Box (LogStep port true emitter count topics offset size) (fun _ => False) before := by
  intro after hs
  have h := hs.1
  rw [logAdapter_static] at h
  cases h

end Solidity.Yul.World.AdapterRules
