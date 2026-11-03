import Solidity.Yul.World.CreationRules
import Solidity.Yul.World.AdapterChecks

/-! Inhabited constructor-boundary controls, not reachable initcode certification. -/
namespace Solidity.Yul.World.CreationFramesChecks
open Solidity.Source
open Solidity.Source.StateExamples
open Solidity.Yul.World.Checks
open Solidity.Yul.World.AdapterChecks (observed memory)
open Solidity.Roadmap (Word Bytes Outcome)

/-- Caller prefix has both event/log observations and two journal entries. -/
def prepared : ObservedEffects D₀ LW LW :=
  { observed with effects := { observed.effects with
      execution := fundedPrefix.apply (creationNonceOp (addr 1)), returndata := [] } }

theorem actual_preparation : prepareCreation observed (addr 1) = some prepared :=
  prepareCreation_exact _ _ (by decide)

theorem nonce_control :
    prepared.effects.execution.journal.length = 3 ∧
    (prepared.effects.execution.world.accounts (addr 1)).nonce = 4 ∧
    (prepared.effects.execution.world.accounts (addr 1)).balance = toWord 100 ∧
    (prepared.effects.execution.world.accounts (addr 1)).code = some 7 ∧
    (prepared.effects.execution.world.accounts (addr 1)).storage.read countPath = some eight ∧
    prepared.effects.execution.world.accounts (addr 2) = fundedPrefix.world.accounts (addr 2) ∧
    prepared.trace = callerTrace ∧ prepared.effects.returndata = [] :=
  ⟨rfl,rfl,rfl,rfl,rfl,creationNonce_other _ _ _ (by decide),rfl,rfl⟩

def parent : CallFrame := fundedPrefix.enter (addr 1) (addr 2) (toWord 9) [222,173] false

def frame : CallFrame := constructorFrame prepared.effects.execution parent (addr 3) (toWord 5)

theorem context_control : frame.input = [] ∧ frame.caller = addr 1 ∧ frame.this = addr 3 ∧
    frame.value = toWord 5 ∧ frame.mark = 3 := ⟨rfl,rfl,rfl,rfl,rfl⟩

def answer (failed : Bool) : FrameAnswer D₀ LW LW :=
  ⟨havoc,calleeTrace,if failed then .revert [253,254] else .success [96,0]⟩

def completed (failed : Bool) := finishCreation prepared frame (answer failed)

theorem failure_control :
    (completed true).effects.execution = prepared.effects.execution ∧
    (completed true).trace = rollbackTrace callerTrace calleeTrace ∧
    (completed true).effects.returndata = [253,254] ∧
    ((completed true).effects.execution.world.accounts (addr 1)).nonce = 4 := by
  have h := failedCreation_keeps_nonce observed (addr 1) (by decide) prepared actual_preparation
    frame havoc calleeTrace [253,254]
  exact ⟨h.1,h.2,rfl,congrArg (fun s => (s.world.accounts (addr 1)).nonce) h.1⟩

theorem success_control :
    (completed false).effects.execution = prepared.effects.execution.run havoc ∧
    (completed false).trace = callerTrace ++ calleeTrace ∧
    (completed false).effects.returndata = [] ∧
    (answer false).outcome = .success [96,0] := ⟨rfl,rfl,rfl,rfl⟩

def laterFrame (failed : Bool) : CallFrame :=
  constructorFrame (completed failed).effects.execution parent (addr 3) (toWord 5)

theorem actual_later_marks : (laterFrame true).mark = 3 ∧ (laterFrame false).mark = 4 := ⟨rfl,rfl⟩

/-- A later successful constructor clears earlier revert data, and a subsequent
failed constructor exposes only its own bytes. Ordered prefixes remain whole. -/
theorem repeated_buffers :
    (finishCreation (completed true) (laterFrame true) (answer false)).effects.returndata = [] ∧
    (finishCreation (completed false) (laterFrame false) (answer true)).effects.returndata = [253,254] ∧
    (finishCreation (completed true) (laterFrame true) (answer false)).trace =
      rollbackTrace callerTrace calleeTrace ++ calleeTrace := ⟨rfl,rfl,rfl⟩

theorem enclosing_revert : fundedPrefix.journal.length = 2 ∧
    (fundedPrefix.enter (addr 1) (addr 2) (toWord 9) [222,173] false).rollback
      ((((fundedPrefix.run callOps).apply (creationNonceOp (addr 1))).run havoc).run callOps) = fundedPrefix :=
  ⟨rfl,creation_outer_rollback _ _ _ _ _ _ _ _ _ _⟩

/-- Real target-memory loading; producer distinguishes code from calldata. -/
def producer : InitcodePort D₀ LW LW := fun _ gas context code =>
  if context.input = [] ∧ code = [17,34,51] ∧ context.this = addr 3 ∧
      context.caller = addr 1 ∧ context.value = toWord 5 ∧ gas = toWord 100000 then
    some (answer false) else none

theorem actual_initcode_load :
    (initcodeAdapter TargetMemory.port producer prepared memory parent (addr 3)
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3)).map
      (fun result => (result.initialization,result.observed.trace,result.observed.effects.returndata)) =
      some (.success [96,0],callerTrace ++ calleeTrace,[]) := by
  rw [initcodeAdapter_exact _ _ _ _ _ _ _ _ _ _ [17,34,51] (answer false) rfl
    Solidity.Yul.World.AdapterChecks.input_loaded (by rfl)]
  rfl

theorem initcode_negative_controls :
    initcodeAdapter TargetMemory.port producer prepared memory parent (addr 3)
      (toWord 100000) (toWord 5) (toWord 0) (toWord 1) = none ∧
    initcodeAdapter TargetMemory.port producer prepared memory {parent with static := true} (addr 3)
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) = none ∧
    (completed false).effects.returndata ≠ [96,0] ∧
    (completed true).effects.execution ≠ fundedPrefix := by
  refine ⟨rfl,initcodeAdapter_static _ _ _ _ _ _ _ _ _ _ rfl,by decide,?_⟩
  intro h
  have hn := congrArg (fun s => (s.world.accounts (addr 1)).nonce) h
  have he := failure_control.1
  rw [he] at hn
  contradiction

def capped : ObservedEffects D₀ LW LW := { observed with effects := { observed.effects with
  execution := fundedPrefix.apply (.account (addr 1) (fun a => {a with nonce := 2^64-1})) } }

theorem cap_refusal : prepareCreation capped (addr 1) = none :=
  prepareCreation_refused _ _ (by decide)

def nearCap : ObservedEffects D₀ LW LW := { observed with effects := { observed.effects with
  execution := fundedPrefix.apply (.account (addr 1) (fun a => {a with nonce := 2^64-2})) } }

theorem cap_boundary_permitted :
    (prepareCreation nearCap (addr 1)).map (fun s => (s.effects.execution.world.accounts (addr 1)).nonce) =
      some (2^64-1) := rfl

theorem memory_refusal :
    initcodeAdapter TargetMemory.port producer prepared memory parent (addr 3)
      (toWord 100000) (toWord 5) ⟨2^256-1,by decide⟩ (toWord 2) = none := rfl

/-- Both success-then-failure and child-commit/enclosing-failure keep the full
ordered interaction list; they never retain failed-frame logs. -/
theorem nested_trace_controls :
    rollbackTrace callerTrace (calleeTrace ++ calleeTrace) =
      callerTrace ++ discardLogs calleeTrace ++ discardLogs calleeTrace ∧
    rollbackTrace callerTrace (rollbackTrace calleeTrace calleeTrace) =
      rollbackTrace callerTrace (calleeTrace ++ calleeTrace) :=
  ⟨rollbackTrace_append_suffix _ _ _,rollbackTrace_nested _ _ _⟩

def initResult : CompletedCreation D₀ LW LW := ⟨.success [96,0],completed false,rfl⟩

theorem init_result_exact :
    initcodeAdapter TargetMemory.port producer prepared memory parent (addr 3)
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) = some initResult :=
  initcodeAdapter_exact _ _ _ _ _ _ _ _ _ _ [17,34,51] (answer false) rfl
    Solidity.Yul.World.AdapterChecks.input_loaded rfl

theorem rule_use : AdapterRules.Box
    (CreationRules.InitStep TargetMemory.port producer parent (addr 3)
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) (.success [96,0]))
    (fun after => after.observed = completed false ∧ after.memory = memory ∧
      after.observed.effects.returndata = []) ⟨prepared,memory⟩ :=
  CreationRules.initcode_step_eq _ _ _ _ _ _ _ _ _ initResult init_result_exact

theorem wrong_outcome_refused : ¬ CreationRules.InitStep TargetMemory.port producer parent (addr 3)
    (toWord 100000) (toWord 5) (toWord 7) (toWord 3) (.revert [96,0])
    ⟨prepared,memory⟩ ⟨completed false,memory⟩ := by
  intro hs
  obtain ⟨result,hr,ho,_⟩ := hs
  rw [init_result_exact] at hr
  cases Option.some.inj hr
  cases ho

def failedProducer : InitcodePort D₀ LW LW := fun s gas context code =>
  (producer s gas context code).map (fun _ => answer true)

def failedResult : CompletedCreation D₀ LW LW := ⟨.revert [253,254],completed true,rfl⟩

theorem failed_result_exact :
    initcodeAdapter TargetMemory.port failedProducer prepared memory parent (addr 3)
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) = some failedResult :=
  initcodeAdapter_exact _ _ _ _ _ _ _ _ _ _ [17,34,51] (answer true) rfl
    Solidity.Yul.World.AdapterChecks.input_loaded rfl

theorem failed_rule_use : AdapterRules.Box
    (CreationRules.InitStep TargetMemory.port failedProducer parent (addr 3)
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) (.revert [253,254]))
    (fun after => after.observed = completed true ∧ after.memory = memory ∧
      after.observed.effects.returndata = [253,254]) ⟨prepared,memory⟩ :=
  CreationRules.initcode_step_eq _ _ _ _ _ _ _ _ _ failedResult failed_result_exact

theorem static_rule_use : AdapterRules.Box
    (CreationRules.InitStep TargetMemory.port producer {parent with static := true} (addr 3)
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) (.success [96,0]))
    (fun _ => False) ⟨prepared,memory⟩ :=
  CreationRules.static_initcode_rule _ _ _ _ _ _ _ _ _ _ rfl

end Solidity.Yul.World.CreationFramesChecks
