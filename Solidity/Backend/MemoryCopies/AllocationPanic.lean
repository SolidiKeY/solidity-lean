import Solidity.Backend.MemoryCopies.AllocationPanicInterface
import Solidity.Backend.MemoryCopies.SourceSize
import Solidity.Backend.Failure.SliceChecks

/-! Source allocation-panic premises select the already proved exact byte
emitter. No Source failure, allocation-size selector or gas model is invented. -/
namespace Solidity.Backend.MemoryCopies
open Solidity.Backend

def panic41Emission {E : Source.Env} {Γ : Source.RCtx} {α : Type}
    {operation : Source.EM E Γ α} {before reached : Source.EMState E Γ}
    (source : Panic41Premise operation before reached) (offset : Nat)
    (machine : Failure.Slice.Machine) (fits : Failure.Fits offset (Source.panicData .alloc))
    (stack : machine.stack.length + 2 ≤ 1024) :
    Panic41EmissionCertificate operation before reached offset machine where
  source := source.failure
  target := fun suffix => Solidity.Lowering.V08.LiteralFailureLowering.panic_checked .alloc offset suffix machine fits stack

theorem panic41_packet_length : (Source.panicData .alloc).length = 36 := by
  decide +kernel

/-- The reused emitter produces 108 byte-write instructions and its terminal. -/
theorem panic41_code_length (offset : Nat) : (panic41Code offset).length = 111 := by
  rw [panic41Code, Failure.emit_length]
  simp only [Solidity.Lowering.V08.LiteralFailureLowering.panic_bytes, panic41_packet_length]

/-- Scratch writes frame every byte outside the exact emitted packet. -/
theorem panic41_memory_frame (offset address : Nat) (machine : Failure.Slice.Machine)
    (outside : address < offset ∨ offset + (Source.panicData .alloc).length ≤ address) :
    Failure.Slice.putBytes machine.memory offset (Source.panicData .alloc) address =
      machine.memory address := by
  simpa only [Solidity.Lowering.V08.LiteralFailureLowering.panic_bytes] using
    Failure.emitted_memory_frame offset address (Solidity.Lowering.V08.LiteralFailureLowering.panicInput .alloc) machine
      (by simpa only [Solidity.Lowering.V08.LiteralFailureLowering.panic_bytes] using outside)

/-- Projection retains the exact packet and distinguishes unsupported slice
execution from a successful terminal revert. -/
theorem panic41_outcome (offset : Nat) (machine : Failure.Slice.Machine)
    (fits : Failure.Fits offset (Source.panicData .alloc))
    (stack : machine.stack.length + 2 ≤ 1024) (suffix : Program) :
    (Failure.Slice.checkedRun (panic41Code offset ++ suffix) machine).map (fun out => out.2) =
      some (some (Source.revertOutcome (Source.panicData .alloc))) := by
  rw [show Failure.Slice.checkedRun (panic41Code offset ++ suffix) machine = _ from
    Solidity.Lowering.V08.LiteralFailureLowering.panic_checked .alloc offset suffix machine fits stack]
  rfl

namespace PanicControls
private def input {E : Source.Env} (state : Source.St E) : Source.EMState E [.int .u256] :=
  (.cons (.int (2 ^ 64) (by decide)) .nil, state)
private def expression {E : Source.Env} : Source.RExpr E [.int .u256] (.bytes .memory) :=
  .newArray rfl (.local .here) rfl

def oversized_panic {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (state : Source.St E) :
    Panic41Premise (Source.evalE global frame 2 expression) (input state) (input state) where
  failure := by
    have premises : NewArrayLengthPanicInputs global frame 1 (τ := .bytes .memory) rfl
        (.local .here) rfl (.val (.int (2 ^ 64) (by decide))) (2 ^ 64) (input state) (input state) :=
      ⟨rfl, rfl, Nat.le_refl _⟩
    exact premises.failure

/-- A real oversize new-array run, at arbitrary actual Source globals/state,
inhabits the combined source-state and emitted-target certificate. -/
def oversized_emission {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (state : Source.St E) :
    Panic41EmissionCertificate (Source.evalE global frame 2 expression)
      (input state) (input state) 31 Failure.markedMachine :=
  panic41Emission (oversized_panic global frame state) 31 Failure.markedMachine
    (by unfold Failure.Fits; decide +kernel) (by decide)

/-- Emission crosses a word boundary and halts before an arbitrary suffix. -/
theorem marked_emission (suffix : Program) :
    Failure.Slice.checkedRun (panic41Code 31 ++ suffix) Failure.markedMachine =
      some ({Failure.markedMachine with memory := (Failure.Slice.putBytes Failure.markedMemory 31
        (Source.panicData .alloc))}, some (Source.revertOutcome (Source.panicData .alloc))) :=
  Solidity.Lowering.V08.LiteralFailureLowering.panic_checked .alloc 31 suffix Failure.markedMachine
    (by unfold Failure.Fits; decide +kernel) (by decide)

/-- Wrong panic, empty revert and unsupported execution are distinct results. -/
theorem wrong_outcomes_rejected (suffix : Program) :
    let observed := (Failure.Slice.checkedRun (panic41Code 31 ++ suffix) Failure.markedMachine).map
      (fun out => out.2)
    observed ≠ some (some (Source.revertOutcome (Source.panicData .index))) ∧
      observed ≠ some (some (Source.revertOutcome [])) ∧ observed ≠ none := by
  dsimp only
  rw [panic41_outcome 31 Failure.markedMachine
    (by unfold Failure.Fits; decide +kernel) (by decide) suffix]
  decide +kernel

/-- Horizon exhaustion cannot supply the allocation-panic source premise. -/
theorem timeout_not_panic {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (state : Source.St E) :
    ¬ Panic41Premise (Source.evalE global frame 0 expression) (input state) (input state) := by
  intro premise
  cases congrArg (fun result => result.1) premise.failure

/-- Successful zero-length allocation cannot supply an allocation-panic premise. -/
theorem zero_length_not_panic {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (state : Source.St E) :
    let before : Source.EMState E [.int .u256] := (.cons (.int 0 (by decide)) .nil, state)
    ¬ Panic41Premise (Source.evalE global frame 2 expression) before before := by
  dsimp only
  intro premise
  cases congrArg (fun result => result.1) premise.failure

end PanicControls
#print axioms panic41Emission
#print axioms panic41_code_length
#print axioms panic41_packet_length
#print axioms panic41_memory_frame
#print axioms panic41_outcome
#print axioms PanicControls.oversized_panic
#print axioms PanicControls.oversized_emission
#print axioms PanicControls.marked_emission
#print axioms PanicControls.wrong_outcomes_rejected
#print axioms PanicControls.timeout_not_panic
#print axioms PanicControls.zero_length_not_panic
end Solidity.Backend.MemoryCopies
