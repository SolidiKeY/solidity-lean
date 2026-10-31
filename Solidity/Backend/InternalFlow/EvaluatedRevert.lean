import Solidity.Backend.InternalFlow.FrameLaws
import Solidity.Backend.InternalFlow.RootAdapter

/-! Actual evaluated intrinsic revert payloads consumed by the published checked
emitter. This is result-to-component wiring, not a VM State representation or
compiler/world simulation. Panic/exhaustion/divergence are never inferred from
THalt.data, which loses those distinctions. No evaluator or codec is defined. -/
namespace Solidity.Backend.InternalFlow
open Backend.Failure

/-- Only normalized ordinary/byte reverts. A noncanonical revertWith [] is
also refused; actual revertData normalizes it to bare revert via ofData. -/
def canonicalRevertInput : THalt → Option Input
  | .revert => some (.custom [])
  | .revertWith (b :: bs) => some (.custom (b :: bs))
  | .panic | .exhausted | .diverge | .revertWith [] => none

/-- Feed an ACTUAL runtime result to existing emit/checkedRun. The machine is
an explicit independent representation hook, not a recovered failed State. -/
def checkedRuntimeRevert {α : Type} (runtime : TRes α) (offset : Nat)
    (suffix : Program) (machine : Slice.Machine) : Option (Slice.Machine × Option Roadmap.Outcome) :=
  match runtime with
  | .ok _ => none
  | .error halt => (canonicalRevertInput halt).bind fun input =>
      Slice.checkedRun (emit offset input ++ suffix) machine

/-- Same result coupling into the published local projected-journal emitter.
Checkpoint/live machine representation remains an explicit external hook. -/
def localRuntimeRevert {α P T : Type} (runtime : TRes α) (saved : Local.Checkpoint P T)
    (offset : Nat) (live : Local.Journal P T) : Option (Local.Journal P T × Roadmap.Outcome) :=
  match runtime with
  | .ok _ => none
  | .error halt => (canonicalRevertInput halt).bind fun input => Local.execute saved offset input live

theorem canonical_ofData (bytes : List UInt8) :
    canonicalRevertInput (THalt.ofData bytes) = some (.custom bytes) := by
  cases bytes <;> rfl

theorem data_of_normalized_revert (bytes : List UInt8) : (THalt.ofData bytes).data = bytes := by
  cases bytes <;> rfl

/-- The runtime's own ordered mapM/flatten evaluation, not a supplied codec. -/
theorem evaluated_revert_execution {C : Contract} {Γ : Ctx} (state : State C Γ)
    (parts : List (RevPart C Γ)) (chunks : List (List UInt8))
    (evaluated : parts.mapM (·.evalT state) = .ok chunks) :
    TRun.revertData parts state = .error (THalt.ofData chunks.flatten) := by
  unfold TRun.revertData
  rw [evaluated]
  rfl

theorem checked_runtime_revert {α : Type} (runtime : TRes α) (bytes : List UInt8)
    (failed : runtime = .error (THalt.ofData bytes)) (offset : Nat)
    (suffix : Program) (machine : Slice.Machine) (fits : Fits offset bytes)
    (stack : machine.stack.length + 2 ≤ 1024) :
    checkedRuntimeRevert runtime offset suffix machine =
      some ({ machine with memory := Slice.putBytes machine.memory offset bytes }, some (.revert bytes)) := by
  simp only [checkedRuntimeRevert, failed, canonical_ofData, Option.bind_some]
  exact checkedRun_emit_suffix offset (.custom bytes) suffix machine fits stack

/-- The emitted bytes are selected by evaluation of these actual payload
parts, through the actual statement result. No free bytes/live-state oracle. -/
theorem checked_evaluated_revert {C : Contract} {Γ : Ctx} (state : State C Γ)
    (parts : List (RevPart C Γ)) (chunks : List (List UInt8))
    (evaluated : parts.mapM (·.evalT state) = .ok chunks) (offset : Nat)
    (suffix : Program) (machine : Slice.Machine) (fits : Fits offset chunks.flatten)
    (stack : machine.stack.length + 2 ≤ 1024) :
    checkedRuntimeRevert (TRun.revertData parts state) offset suffix machine =
      some ({ machine with memory := Slice.putBytes machine.memory offset chunks.flatten },
        some (.revert chunks.flatten)) :=
  checked_runtime_revert _ _ (evaluated_revert_execution state parts chunks evaluated) offset suffix machine fits stack

/-- Arguments and byte evaluation in the actual entered dependent call frame
are both explicit execution premises, not a desired simulation hypothesis. -/
theorem checked_call_evaluated_revert {C : Contract} {Γ Δ ps rs : Ctx}
    (caller : State C Γ) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (arguments : TEnv C caller.H ps) (ha : args.evalT caller = .ok arguments)
    (parts : List (RevPart C (rs ++ ps))) (chunks : List (List UInt8))
    (evaluated : parts.mapM (·.evalT (ret.enterT (caller.withEnv arguments)).st) = .ok chunks)
    (offset : Nat) (suffix : Program) (machine : Slice.Machine) (fits : Fits offset chunks.flatten)
    (stack : machine.stack.length + 2 ≤ 1024) :
    checkedRuntimeRevert (TRun.call args ret .refl (TRun.revertData parts) caller) offset suffix machine =
      some ({ machine with memory := Slice.putBytes machine.memory offset chunks.flatten },
        some (.revert chunks.flatten)) := by
  have bodyFailure : TRun.revertData parts (ret.enterT (caller.withEnv arguments)).st =
      .error (THalt.ofData chunks.flatten) :=
    evaluated_revert_execution _ parts chunks evaluated
  have callFailure : TRun.call args ret .refl (TRun.revertData parts) caller =
      .error (THalt.ofData chunks.flatten) :=
    call_body_failure args ret .refl (TRun.revertData parts) caller arguments ha _ bodyFailure
  exact checked_runtime_revert _ _ callFailure offset suffix machine fits stack

theorem local_runtime_revert {α P T : Type} (runtime : TRes α) (bytes : List UInt8)
    (failed : runtime = .error (THalt.ofData bytes)) (saved : Local.Checkpoint P T)
    (offset : Nat) (live : Local.Journal P T) (fits : Fits offset bytes)
    (stack : live.machine.stack.length + 2 ≤ 1024) :
    localRuntimeRevert runtime saved offset live = some (Local.restore saved, .revert bytes) := by
  simp only [localRuntimeRevert, failed, canonical_ofData, Option.bind_some]
  exact Local.execute_failure saved offset bytes live fits stack

/-- Live projections come from the actual pre-revert State. The separately
supplied slice machine is not identified with its heap/locals/target frame. -/
theorem local_evaluated_revert {C : Contract} {Γ : Ctx} {P T : Ty}
    (persistent : Storage.RegionRoot C false P) (transient : Storage.RegionRoot C true T)
    (state : State C Γ) (parts : List (RevPart C Γ)) (chunks : List (List UInt8))
    (evaluated : parts.mapM (·.evalT state) = .ok chunks)
    (saved : Storage C) (caller machine : Slice.Machine) (offset : Nat)
    (fits : Fits offset chunks.flatten) (stack : machine.stack.length + 2 ≤ 1024) :
    localRuntimeRevert (TRun.revertData parts state)
      (Local.save (rootJournal persistent transient saved caller)) offset
      (rootJournal persistent transient state.storage machine) =
      some (rootJournal persistent transient saved caller, .revert chunks.flatten) :=
  local_runtime_revert _ _ (evaluated_revert_execution state parts chunks evaluated) _ offset _ fits stack

/-- Empty data projections cannot justify converting another halt class. -/
theorem refused_empty_classes {α : Type} (offset : Nat) (suffix : Program) (machine : Slice.Machine) :
    checkedRuntimeRevert (.error .panic : TRes α) offset suffix machine = none ∧
    checkedRuntimeRevert (.error .exhausted : TRes α) offset suffix machine = none ∧
    checkedRuntimeRevert (.error .diverge : TRes α) offset suffix machine = none ∧
    checkedRuntimeRevert (.error (.revertWith []) : TRes α) offset suffix machine = none := ⟨rfl,rfl,rfl,rfl⟩

theorem local_refused_empty_classes {α P T : Type} (saved : Local.Checkpoint P T)
    (offset : Nat) (live : Local.Journal P T) :
    localRuntimeRevert (.error .panic : TRes α) saved offset live = none ∧
    localRuntimeRevert (.error .exhausted : TRes α) saved offset live = none ∧
    localRuntimeRevert (.error .diverge : TRes α) saved offset live = none ∧
    localRuntimeRevert (.error (.revertWith []) : TRes α) saved offset live = none := ⟨rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.InternalFlow.canonical_ofData' does not depend on any axioms -/
#guard_msgs in
#print axioms canonical_ofData
/-- info: 'Solidity.Backend.InternalFlow.data_of_normalized_revert' does not depend on any axioms -/
#guard_msgs in
#print axioms data_of_normalized_revert
/-- info: 'Solidity.Backend.InternalFlow.evaluated_revert_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evaluated_revert_execution
/-- info: 'Solidity.Backend.InternalFlow.checked_runtime_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_runtime_revert
/-- info: 'Solidity.Backend.InternalFlow.checked_evaluated_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_evaluated_revert
/-- info: 'Solidity.Backend.InternalFlow.checked_call_evaluated_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_call_evaluated_revert
/-- info: 'Solidity.Backend.InternalFlow.local_runtime_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms local_runtime_revert
/-- info: 'Solidity.Backend.InternalFlow.local_evaluated_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms local_evaluated_revert
/-- info: 'Solidity.Backend.InternalFlow.refused_empty_classes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms refused_empty_classes
/-- info: 'Solidity.Backend.InternalFlow.local_refused_empty_classes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms local_refused_empty_classes

end Solidity.Backend.InternalFlow
