import Solidity.Yul.World.AdapterRules
import Solidity.Yul.World.ByteMemory
import Solidity.Yul.World.WorldChecks

/-! Kernel consumer controls. Scripted WorldPort witnesses exercise actual typed
journal operations, not a claim that they are reachable G42/solc callees. -/
namespace Solidity.Yul.World.AdapterChecks
open Solidity.Source
open Solidity.Source.StateExamples
open Solidity.Roadmap (Bytes Word)
open Solidity.Yul.World.Checks
open Solidity.Backend.Environment (Memory readMemory writeBytes)

def observed : ObservedEffects D₀ LW LW :=
  ⟨⟨fundedPrefix, [l0, l4], [9, 8, 7]⟩, callerTrace, rfl⟩

def memory : Memory := writeBytes (fun _ => 255) 7 [17, 34, 51]

def answer (fail : Bool) (input : Bytes) : FrameAnswer D₀ LW LW :=
  ⟨havoc, calleeTrace, if fail then .revert input else .success input⟩

def producer (fail : Bool) : WorldPort D₀ LW LW := fun _ _ _ _ _ input => some (answer fail input)

def parent : CallFrame := fundedPrefix.enter (addr 1) (addr 2) (toWord 0) [] false

theorem input_loaded : TargetMemory.port.load memory (toWord 7) (toWord 3) = some [17, 34, 51] := by
  rw [TargetMemory.load_exact _ _ _ (by decide)]
  exact congrArg some (Solidity.Backend.Environment.read_written [17, 34, 51] 7 (fun _ => 255))

def done (fail : Bool) := finishObserved observed
  (childContext fundedPrefix parent .call (addr 3) (toWord 0) [17, 34, 51]) (answer fail [17, 34, 51])

/-- Real input load and producer invocation return the same typed completed
call; output writes a two-byte prefix, while returndata retains all three. -/
theorem call_plumbing (fail : Bool) :
    (callAdapter TargetMemory.port (producer fail) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map
      (fun c => (c.observed.effects.returndata, c.outcome, c.copiedMemory.map (fun m => readMemory m 31 3))) =
      some ([17, 34, 51], (answer fail [17, 34, 51]).outcome, some [17, 34, 255]) := by
  rw [callAdapter_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl input_loaded rfl]
  cases fail <;> rfl

/-- Failure preserves the nonempty caller journal and every caller observation,
removes only failed logs and exposes the raw callee failure bytes. -/
theorem reverted_call :
    (done true).effects.execution = fundedPrefix ∧
    (done true).trace = rollbackTrace callerTrace calleeTrace ∧
    (done true).effects.returndata = [17, 34, 51] ∧
    callFlag (answer true [17, 34, 51]).outcome = toWord 0 := by
  have h := (finishObserved_revert observed
    (childContext fundedPrefix parent .call (addr 3) (toWord 0) [17, 34, 51]) havoc calleeTrace [17, 34, 51]).1
  exact ⟨congrArg Effects.execution h, rfl, rfl, rfl⟩

theorem successful_call :
    ((done false).effects.execution.world.accounts (addr 1)).storage.read countPath = some seven ∧
    (done false).trace = callerTrace ++ calleeTrace ∧
    callFlag (answer false [17, 34, 51]).outcome = toWord 1 := ⟨rfl, rfl, rfl⟩

/-- Concrete returndata source-end check and destination-memory framing. -/
theorem actual_copy :
    (copyReturndata TargetMemory.port (done true).effects memory (toWord 31) (toWord 1) (toWord 2)).map
      (fun m => (readMemory m 31 2, m 30, m 33)) = some ([34, 51], 255, 255) ∧
    copyReturndata TargetMemory.port (done true).effects memory (toWord 31) (toWord 4) (toWord 0) = none := by
  exact ⟨rfl, copyReturndata_bounds _ _ _ _ _ _ (by decide)⟩

/-- A destination refusal after an invocation does not erase that invocation's
outcome or full observations. It remains an explicit unresolved copy result. -/
def refusingPort : BytePort Memory := { TargetMemory.port with store := fun _ _ _ => none }

theorem refused_output_keeps_trace :
    (callAdapter refusingPort (producer true) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map
      (fun c => (c.observed.trace, c.outcome, c.copiedMemory.isNone)) =
      some (rollbackTrace callerTrace calleeTrace, .revert [17, 34, 51], true) := by
  rw [callAdapter_exact refusingPort (producer true) observed memory parent .call (addr 3)
    (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2) [17, 34, 51] (answer true [17, 34, 51])
    rfl rfl input_loaded rfl]
  rfl

theorem refused_success_keeps_writes :
    (callAdapter refusingPort (producer false) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map
      (fun c => (c.observed.trace, c.outcome, c.copiedMemory.isNone,
        (c.observed.effects.execution.world.accounts (addr 1)).storage.read countPath)) =
      some (callerTrace ++ calleeTrace, .success [17, 34, 51], true, some seven) := by
  rw [callAdapter_exact refusingPort (producer false) observed memory parent .call (addr 3)
    (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2) [17, 34, 51] (answer false [17, 34, 51])
    rfl rfl input_loaded rfl]
  rfl

theorem static_value_preflight_control :
    callAdapter TargetMemory.port (producer false) observed memory { parent with static := true } .call (addr 3)
      (toWord 100000) (toWord 1) (toWord 7) (toWord 3) (toWord 31) (toWord 2) = none :=
  callAdapter_static_value_refusal _ _ _ _ _ _ _ _ _ _ _ _ rfl (by decide)

/-- A delegated storage frame alone cannot select library code. The actual
producer receives the explicit target separately from the inherited frame. -/
def targetProducer : WorldPort D₀ LW LW := fun _ _ target _ _ _ =>
  some ⟨[], [], .success (if target = addr 3 then [33] else [44])⟩

theorem delegate_target_controls :
    (callAdapter TargetMemory.port targetProducer observed memory parent .delegatecall (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map (fun c => c.outcome) = some (.success [33]) ∧
    (callAdapter TargetMemory.port targetProducer observed memory parent .delegatecall (addr 4)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map (fun c => c.outcome) = some (.success [44]) := by
  constructor <;> rw [callAdapter_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl input_loaded rfl] <;> rfl

def otherHistory : ObservedEffects D₀ LW LW :=
  ⟨observed.effects, observed.trace ++ [.event (.credit (addr 9) (toWord 5))], by
    simp only [logs_append, committedLogs, List.append_nil, observed.logs_eq]⟩

def historyProducer : WorldPort D₀ LW LW := fun prior _ _ _ _ _ =>
  some ⟨[], [], .success [UInt8.ofNat prior.trace.length]⟩

/-- Identical worlds with different interaction histories remain distinct
producer inputs, as required for history-dependent environment strategies. -/
theorem history_sensitive_controls :
    otherHistory.effects.execution = observed.effects.execution ∧
    (callAdapter TargetMemory.port historyProducer observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map (fun c => c.outcome) = some (.success [4]) ∧
    (callAdapter TargetMemory.port historyProducer otherHistory memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map (fun c => c.outcome) = some (.success [5]) := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [callAdapter_exact TargetMemory.port historyProducer observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2) [17, 34, 51] _ rfl rfl input_loaded rfl]
    rfl
  · rw [callAdapter_exact TargetMemory.port historyProducer otherHistory memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2) [17, 34, 51] _ rfl rfl input_loaded rfl]
    rfl

def lastAddress : Word := ⟨2^256 - 1, by decide⟩

/-- Even when a returned prefix would fit, the full requested two-byte output
window is refused before invocation at the last representable byte address. -/
theorem real_capacity_refusal :
    callAdapter TargetMemory.port targetProducer observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) lastAddress (toWord 2) = none := rfl

theorem real_destination_controls :
    TargetMemory.port.store memory lastAddress [17, 34] = none ∧
    copyReturndata TargetMemory.port (done true).effects memory lastAddress (toWord 3) (toWord 0) = some memory :=
  ⟨rfl, rfl⟩

def loadedLog : Log := ⟨addr 3, ⟨2, by decide⟩, #v[toWord 5, toWord 6], [17, 34, 51]⟩

theorem loaded_log_controls :
    (logAdapter TargetMemory.port observed memory false (addr 3) ⟨2, by decide⟩
      #v[toWord 5, toWord 6] (toWord 7) (toWord 3)).map (fun s => s.trace) =
      some (callerTrace ++ [.log loadedLog]) ∧
    logAdapter TargetMemory.port observed memory true (addr 3) ⟨2, by decide⟩
      #v[toWord 5, toWord 6] (toWord 7) (toWord 3) = none := by
  constructor
  · rw [logAdapter_exact _ _ _ _ _ _ _ _ _ input_loaded]
    rfl
  · rfl

theorem loaded_log_revert :
    (finishObserved observed parent ⟨havoc, calleeTrace ++ [.log loadedLog], .revert [254]⟩).effects =
      ⟨fundedPrefix, [l0, l4], [254]⟩ ∧
    (finishObserved observed parent ⟨havoc, calleeTrace ++ [.log loadedLog], .revert [254]⟩).trace =
      rollbackTrace callerTrace calleeTrace := finishObserved_logged_revert _ _ _ _ _ _

/-- Successful child storage/log effects form the exact prefix of a later
failure, including a nonempty source journal and complete mixed observations. -/
theorem nested_failure_control :
    (finishObserved (done false) (childContext (done false).effects.execution parent .call (addr 4) (toWord 0) []) ⟨callOps, [.log loadedLog, .event (.credit (addr 8) (toWord 10))], .revert []⟩).effects.execution =
      (done false).effects.execution ∧
    (finishObserved (done false) (childContext (done false).effects.execution parent .call (addr 4) (toWord 0) []) ⟨callOps, [.log loadedLog, .event (.credit (addr 8) (toWord 10))], .revert []⟩).trace =
      callerTrace ++ calleeTrace ++ [.event (.credit (addr 8) (toWord 10))] := by
  have h := (finishObserved_revert (done false) (childContext (done false).effects.execution parent .call (addr 4) (toWord 0) []) callOps
    [.log loadedLog, .event (.credit (addr 8) (toWord 10))] []).1
  have he := congrArg (fun e : Effects D₀ LW LW => e.execution) h
  exact ⟨he, rfl⟩

theorem loaded_log_negative :
    callerTrace ++ [.log loadedLog] ≠
      callerTrace ++ [.log ⟨addr 3, ⟨2, by decide⟩, #v[toWord 6, toWord 5], [17, 34, 51]⟩] ∧
    callerTrace ++ [.log loadedLog] ≠ callerTrace := by decide

/-- Inhabited local semantic rules over the actual copy/log consumer code.
They are not source dl/tm embeddings or G51 transport certificates. -/
theorem copy_rule_control :
    AdapterRules.Box (AdapterRules.CopyStep TargetMemory.port (toWord 31) (toWord 1) (toWord 2))
      (fun after => after.observed = done true ∧ after.memory = writeBytes memory 31 [34, 51])
      (⟨done true, memory⟩ : AdapterRules.Configuration Memory D₀ LW LW) :=
  AdapterRules.copy_rule _ _ _ _ _ _ rfl

theorem log_rule_control :
    AdapterRules.Box (AdapterRules.LogStep TargetMemory.port false (addr 3) ⟨2, by decide⟩
      #v[toWord 5, toWord 6] (toWord 7) (toWord 3))
      (fun after => after.observed = emitObserved observed loadedLog ∧ after.memory = memory)
      (⟨observed, memory⟩ : AdapterRules.Configuration Memory D₀ LW LW) :=
  AdapterRules.log_rule _ _ _ _ _ _ _ _ (logAdapter_exact _ _ _ _ _ _ _ _ _ input_loaded)

theorem call_rule_control (fail : Bool) :
    AdapterRules.Box (AdapterRules.CallStep TargetMemory.port (producer fail) parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
      (answer fail [17, 34, 51]).outcome)
      (fun after => after.observed = done fail ∧ after.memory = writeBytes memory 31 [17, 34])
      (⟨observed, memory⟩ : AdapterRules.Configuration Memory D₀ LW LW) := by
  let result : CompletedCall Memory D₀ LW LW :=
    ⟨(answer fail [17, 34, 51]).outcome, done fail, by cases fail <;> rfl,
      some (writeBytes memory 31 [17, 34])⟩
  have hc : callAdapter TargetMemory.port (producer fail) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2) = some result := by
    rw [callAdapter_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl input_loaded rfl]
    cases fail <;> rfl
  exact AdapterRules.call_rule TargetMemory.port (producer fail) parent .call (addr 3)
    (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2) ⟨observed, memory⟩ result
    (writeBytes memory 31 [17, 34]) hc rfl

/-- Even with identical return bytes, the call judgment cannot relabel success
as callee revert. Outcome is an explicit index, not an erased existential. -/
theorem wrong_call_outcome_refused (after : AdapterRules.Configuration Memory D₀ LW LW) :
    ¬ AdapterRules.CallStep TargetMemory.port (producer false) parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
      (.revert [17, 34, 51]) ⟨observed, memory⟩ after := by
  intro hs
  obtain ⟨result, hr, ho, _, _⟩ := hs
  rw [callAdapter_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl input_loaded rfl] at hr
  cases Option.some.inj hr
  cases ho

#print axioms call_plumbing
#print axioms reverted_call
#print axioms actual_copy
end Solidity.Yul.World.AdapterChecks
