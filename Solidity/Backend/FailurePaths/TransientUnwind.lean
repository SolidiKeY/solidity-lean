import Solidity.Backend.FailurePaths.Statements
import Solidity.Backend.Transient.SourceFrames

/-!
# P7 composition for a compiled empty failure

This consumes P7 unchanged. The actual source primitive write is followed by a
source bare-revert statement, while the target executes its actual TSTORE code
and the very same code selected by the G38 statement compiler. P7 supports only
empty REVERT; nonempty byte payloads and full EVM correspondence stay open.
-/
namespace Solidity.Backend.FailurePaths.TransientUnwind
open Source

/-- Both published emitters use the same PUSH32 zero operands. -/
theorem empty_code : Failure.emit 0 .empty = Transient.emptyRevert := by rfl

def source {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr) (extra : Nat)
    (slot : Transient.BoolSlot E) (value : Bool) (locals : Locals E.layout Γ) :
    EM E [] (Source.Out E.layout Γ Γ) := do
  Source.writeAt frame slot.path (.bool value)
  Source.execS global frame (extra + 7) 0 none
    (.expr Lowering.V08.LiteralFailureLowering.revertBare : RStmt E [] false .body Γ Γ) locals

/-- The actual evaluator retains the dirty transient write when the statement
reverts. It is the enclosing caller rollback that restores the source store. -/
theorem source_run {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr) (extra : Nat)
    (slot : Transient.BoolSlot E) (normal : frame.static = false) (value : Bool)
    (locals : Locals E.layout Γ) (state : St E) :
    (source global frame extra slot value locals).run (Source.L0 E, state) =
      (.error (.revert []), (Source.L0 E, Transient.sourceWrite slot frame.this value state)) := by
  rw [source, Source.Hoare.run_bind,
    Transient.write_actual slot frame normal value (Source.L0 E, state)]
  rfl

/-- Actual source and actual framed target execution, not a supplied success or
rollback oracle. Caller restoration uses P7's executed TSTORE/REVERT theorem. -/
theorem paired_bare_failure {E : Source.Env} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (extra : Nat) (slot : Transient.BoolSlot E)
    (normal : frame.static = false) (value : Bool) (locals : Locals E.layout Γ)
    (state : St E) (target : Transient.State) :
    compileStatement global 0
      (.expr Lowering.V08.LiteralFailureLowering.revertBare : RStmt E [] false .body Γ Γ) =
      some (Failure.emit 0 .empty) ∧
    (source global frame extra slot value locals).run (Source.L0 E, state) =
      (.error (.revert []), (Source.L0 E, Transient.sourceWrite slot frame.this value state)) ∧
    Transient.callbackInFrame frame
      (Transient.storeCode slot.key (Transient.boolWord value) ++ Failure.emit 0 .empty) target =
      .error .reverted target ∧
    (state.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback
      (Transient.sourceWrite slot frame.this value state).ex = state.ex ∧
    Transient.Represents slot frame.this
      (Source.L0 E, Transient.sourceWrite slot frame.this value state)
      (Transient.write target frame.this slot.key (Transient.boolWord value)) := by
  refine ⟨rfl, source_run global frame extra slot normal value locals state, ?_, ?_,
    Transient.write_represents slot frame.this value (Source.L0 E, state) target⟩
  · rw [empty_code]
    exact Transient.framed_revert frame normal slot.key (Transient.boolWord value) target
  · exact Source.rollback_run state.ex
      [.transient frame.this fun cells => cells.write slot.path (Transient.boolValue slot value)]
      frame.this frame.sender frame.value frame.cd frame.static

/-- Full source-state restoration is valid for this executed transient-only
prefix: its heap, event/log lists and function locals were unchanged by the
write. No analogous claim is made for arbitrary allocating bodies. -/
theorem source_restored {E : Source.Env} (frame : Fr) (slot : Transient.BoolSlot E)
    (value : Bool) (state : St E) :
    {Transient.sourceWrite slot frame.this value state with ex := (
      (state.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback
        (Transient.sourceWrite slot frame.this value state).ex)} = state := by
  have restored := Source.rollback_run state.ex
    [.transient frame.this fun cells => cells.write slot.path (Transient.boolValue slot value)]
    frame.this frame.sender frame.value frame.cd frame.static
  change (state.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback
    (Transient.sourceWrite slot frame.this value state).ex = state.ex at restored
  change {state with ex := _} = state
  rw [restored]

/-- Selected-cell simulation, with the genuine initial relation made explicit.
Both runs are derived and the same relation holds after source caller rollback
and target frame restoration. No full-world representation is inferred. -/
theorem simulates_bare_failure {E : Source.Env} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (extra : Nat) (slot : Transient.BoolSlot E)
    (normal : frame.static = false) (value : Bool) (locals : Locals E.layout Γ)
    (state : St E) (target : Transient.State)
    (represented : Transient.Represents slot frame.this (Source.L0 E, state) target) :
    (source global frame extra slot value locals).run (Source.L0 E, state) =
      (.error (.revert []), (Source.L0 E, Transient.sourceWrite slot frame.this value state)) ∧
    Transient.callbackInFrame frame
      (Transient.storeCode slot.key (Transient.boolWord value) ++ Failure.emit 0 .empty) target =
      .error .reverted target ∧
    Transient.Represents slot frame.this (Source.L0 E,
      {Transient.sourceWrite slot frame.this value state with ex := (
        (state.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback
          (Transient.sourceWrite slot frame.this value state).ex)}) target := by
  have paired := paired_bare_failure global frame extra slot normal value locals state target
  refine ⟨paired.2.1, paired.2.2.1, ?_⟩
  rw [source_restored]
  exact represented

#print axioms empty_code
#print axioms source_run
#print axioms paired_bare_failure
#print axioms source_restored
#print axioms simulates_bare_failure
end Solidity.Backend.FailurePaths.TransientUnwind
