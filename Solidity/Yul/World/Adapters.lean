import Solidity.Yul.World.Frames

/-! # World-side consumer adapters
No alternate world or memory implementation. Producer functions below are
explicit inputs, not assumed adequacy theorems. Physical/source agreement and
actual known/environment reachability are separate named obligations.
-/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
variable {D : Layout} {L T : Address → SPath → STy}

/-- Full observations and their committed-log projection agree intrinsically. -/
structure ObservedEffects (D : Layout) (L T : Address → SPath → STy) where
  effects : Effects D L T
  trace : List Observation
  logs_eq : committedLogs trace = effects.logs

/-- The exact callee boundary consumed here. An actual world producer must
justify these operations/outcome and the FULL ordered trace, not projections. -/
structure FrameAnswer (D : Layout) (L T : Address → SPath → STy) where
  operations : List (Op D L T)
  trace : List Observation
  outcome : Outcome

/-- Consumer interface while the physical package is transferred. No laws are
assumed as fields. An instance is not a source/memory adequacy certificate. -/
structure BytePort (Memory : Type) where
  acceptOutput : Memory → Word → Word → Bool
  load : Memory → Word → Word → Option Bytes
  store : Memory → Word → Bytes → Option Memory

/-- Existing typed world inputs, context and exact raw input bytes. -/
abbrev WorldPort (D : Layout) (L T : Address → SPath → STy) :=
  ObservedEffects D L T → CallKind → Address → Word → CallFrame → Bytes → Option (FrameAnswer D L T)

/-- Call completion preserves all ordered interaction observations on failure,
while the existing typed journal rolls back callee operations and its logs. -/
def finishObserved (entry : ObservedEffects D L T) (frame : CallFrame)
    (answer : FrameAnswer D L T) : ObservedEffects D L T where
  effects := complete entry.effects frame.this frame.caller frame.value frame.input frame.static
    answer.operations (committedLogs answer.trace) answer.outcome
  trace := match answer.outcome with
    | .success _ => entry.trace ++ answer.trace
    | .revert _ => rollbackTrace entry.trace answer.trace
  logs_eq := by
    cases answer.outcome <;> simp only [complete, logs_append, rollback_logs, entry.logs_eq]

/-- Bounded RETURNDATACOPY delegates the destination write to the actual port;
source bounds are checked even at size zero. -/
def copyReturndata {Memory : Type} (port : BytePort Memory) (entry : Effects D L T)
    (memory : Memory) (destination source size : Word) : Option Memory :=
  (returnWindow entry.returndata source.val size.val).bind (port.store memory destination)

/-- A completed world invocation is retained even when the memory producer
refuses the output write. Refusal is not silently recoded as callee revert.
The enclosing source-fault/physical rollback adapter remains a producer input. -/
structure CompletedCall (Memory : Type) (D : Layout) (L T : Address → SPath → STy) where
  outcome : Outcome
  observed : ObservedEffects D L T
  returndata_eq : observed.effects.returndata = returnData outcome
  copiedMemory : Option Memory

/-- Raw CALL/STATICCALL/DELEGATECALL success word. -/
def callFlag : Outcome → Word
  | .success _ => ⟨1, by decide⟩
  | .revert _ => ⟨0, by decide⟩

/-- Caller-side static value restriction, before any producer invocation.
A rejection is an adapter preflight failure, not a callee failure outcome. -/
def callPreflight (parent : CallFrame) (kind : CallKind) (value : Word) : Bool :=
  match kind with
  | .call => if parent.static then decide (value.val = 0) else true
  | .staticcall | .delegatecall => true

/-- Execute input loading, invoke the supplied actual world producer with those
bytes and inherited call context, complete the source journal/trace, and copy
only min(output capacity, actual returndata length) output bytes. -/
def callAdapter {Memory : Type} (port : BytePort Memory) (invoke : WorldPort D L T)
    (entry : ObservedEffects D L T) (memory : Memory) (parent : CallFrame) (kind : CallKind)
    (callee : Address) (gas value inputOffset inputSize outputOffset outputSize : Word) :
    Option (CompletedCall Memory D L T) :=
  if callPreflight parent kind value && port.acceptOutput memory outputOffset outputSize then do
    let input ← port.load memory inputOffset inputSize
    let frame := childContext entry.effects.execution parent kind callee value input
    let answer ← invoke entry kind callee gas frame input
    let completed := finishObserved entry frame answer
    pure ⟨answer.outcome, completed,
      complete_data _ _ _ _ _ _ _ _ _,
      port.store memory outputOffset (callOutput (returnData answer.outcome) outputSize.val)⟩
  else none

theorem copyReturndata_bounds {Memory : Type} (port : BytePort Memory) (entry : Effects D L T)
    (memory : Memory) (destination source size : Word)
    (h : entry.returndata.length < source.val + size.val) :
    copyReturndata port entry memory destination source size = none := by
  have hn : returnWindow entry.returndata source.val size.val = none :=
    (returnWindow_none_iff _ _ _).mpr h
  simp only [copyReturndata, hn, Option.bind_none]

theorem copyReturndata_exact {Memory : Type} (port : BytePort Memory) (entry : Effects D L T)
    (memory : Memory) (destination source size : Word) (bytes : Bytes)
    (h : returnWindow entry.returndata source.val size.val = some bytes) :
    copyReturndata port entry memory destination source size = port.store memory destination bytes := by
  simp only [copyReturndata, h, Option.bind_some]

theorem finishObserved_revert (entry : ObservedEffects D L T) (frame : CallFrame)
    (ops : List (Op D L T)) (trace : List Observation) (data : Bytes) :
    (finishObserved entry frame ⟨ops, trace, .revert data⟩).effects =
      ⟨entry.effects.execution, entry.effects.logs, data⟩ ∧
    (finishObserved entry frame ⟨ops, trace, .revert data⟩).trace = rollbackTrace entry.trace trace := by
  exact ⟨complete_revert entry.effects frame.this frame.caller frame.value frame.input frame.static ops (committedLogs trace) data, rfl⟩

theorem finishObserved_success (entry : ObservedEffects D L T) (frame : CallFrame)
    (ops : List (Op D L T)) (trace : List Observation) (data : Bytes) :
    (finishObserved entry frame ⟨ops, trace, .success data⟩).effects.execution =
      entry.effects.execution.run ops ∧
    (finishObserved entry frame ⟨ops, trace, .success data⟩).trace = entry.trace ++ trace := ⟨rfl, rfl⟩

/-- Actual adapter execution, with concrete producer/port successes explicit.
No inference that an arbitrary supplied producer realizes source/EVM execution. -/
theorem callAdapter_exact {Memory : Type} (port : BytePort Memory) (invoke : WorldPort D L T)
    (entry : ObservedEffects D L T) (memory : Memory) (parent : CallFrame) (kind : CallKind)
    (callee : Address) (gas value inputOffset inputSize outputOffset outputSize : Word)
    (input : Bytes) (answer : FrameAnswer D L T)
    (hp : callPreflight parent kind value = true)
    (ho : port.acceptOutput memory outputOffset outputSize = true)
    (hl : port.load memory inputOffset inputSize = some input)
    (hi : invoke entry kind callee gas
      (childContext entry.effects.execution parent kind callee value input) input = some answer) :
    callAdapter port invoke entry memory parent kind callee gas value inputOffset inputSize outputOffset outputSize =
      some ⟨answer.outcome,
        finishObserved entry (childContext entry.effects.execution parent kind callee value input) answer,
        complete_data _ _ _ _ _ _ _ _ _,
        port.store memory outputOffset (callOutput (returnData answer.outcome) outputSize.val)⟩ := by
  simp only [callAdapter, hp, ho, Bool.true_and, ↓reduceIte, hl, hi, bind, Option.bind_some, pure]

theorem callAdapter_static_value_refusal {Memory : Type} (port : BytePort Memory)
    (invoke : WorldPort D L T) (entry : ObservedEffects D L T) (memory : Memory)
    (parent : CallFrame) (callee : Address) (gas value inputOffset inputSize outputOffset outputSize : Word)
    (hs : parent.static = true) (hv : value.val ≠ 0) :
    callAdapter port invoke entry memory parent .call callee gas value inputOffset inputSize outputOffset outputSize = none := by
  simp only [callAdapter, callPreflight, hs, ↓reduceIte, hv, decide_false, Bool.false_and, Bool.false_eq_true]

/-- Common full-log transition for Yul LOGn and an emit producer's complete
encoding. Existing Source emit topic encoding is still a separate obligation. -/
def emitObserved (entry : ObservedEffects D L T) (log : Log) : ObservedEffects D L T where
  effects := { entry.effects with logs := entry.effects.logs ++ [log] }
  trace := entry.trace ++ [.log log]
  logs_eq := by simp only [logs_append, committedLogs, entry.logs_eq]

/-- Actual payload loading and static refusal for LOG0–LOG4 (topic count is
intrinsic in Log/Vector). The memory producer owns read/ownership agreement. -/
def logAdapter {Memory : Type} (port : BytePort Memory) (entry : ObservedEffects D L T)
    (memory : Memory) (static : Bool) (emitter : Address) (count : Fin 5)
    (topics : Vector Word count.val) (offset size : Word) : Option (ObservedEffects D L T) :=
  if static then none else do
    let bytes ← port.load memory offset size
    pure (emitObserved entry ⟨emitter, count, topics, bytes⟩)

theorem logAdapter_static {Memory : Type} (port : BytePort Memory) (entry : ObservedEffects D L T)
    (memory : Memory) (emitter : Address) (count : Fin 5) (topics : Vector Word count.val) (offset size : Word) :
    logAdapter port entry memory true emitter count topics offset size = none := rfl

theorem logAdapter_exact {Memory : Type} (port : BytePort Memory) (entry : ObservedEffects D L T)
    (memory : Memory) (emitter : Address) (count : Fin 5) (topics : Vector Word count.val) (offset size : Word)
    (bytes : Bytes) (h : port.load memory offset size = some bytes) :
    logAdapter port entry memory false emitter count topics offset size =
      some (emitObserved entry ⟨emitter, count, topics, bytes⟩) := by
  simp only [logAdapter, Bool.false_eq_true, ↓reduceIte, h, bind, Option.bind_some, pure]

theorem emitObserved_world (entry : ObservedEffects D L T) (log : Log) :
    (emitObserved entry log).effects.execution = entry.effects.execution ∧
    (emitObserved entry log).effects.returndata = entry.effects.returndata := ⟨rfl, rfl⟩

/-- A genuine failed child can include logging before it fails; completion
removes that suffix's logs but retains every interaction in order. -/
theorem finishObserved_logged_revert (entry : ObservedEffects D L T) (frame : CallFrame)
    (ops : List (Op D L T)) (trace : List Observation) (log : Log) (data : Bytes) :
    (finishObserved entry frame ⟨ops, trace ++ [.log log], .revert data⟩).effects =
      ⟨entry.effects.execution, entry.effects.logs, data⟩ ∧
    (finishObserved entry frame ⟨ops, trace ++ [.log log], .revert data⟩).trace =
      rollbackTrace entry.trace trace := by
  refine ⟨(finishObserved_revert _ _ _ _ _).1, ?_⟩
  simp only [finishObserved, rollbackTrace, discardLogs_append, discardLogs, List.append_nil]

end Solidity.Yul.World
