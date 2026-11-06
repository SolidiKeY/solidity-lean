import Solidity.Lowering.V08.LiteralFailureLowering
import Solidity.Lowering.V08.SourceCustomErrorControls

namespace Solidity.Lowering.V08.LiteralFailureControls
open Solidity Source Backend
open SourceCustomErrorControls LiteralFailureLowering

def machine : Failure.Slice.Machine :=
  ⟨[⟨77,by decide +kernel⟩], fun x => if x = 4 then 231 else 17⟩
def suffix : Backend.Program := [.op .ADD]

theorem reason_decision {E : Env} {Γ : RCtx} (bytes : Roadmap.Bytes) :
    literalInput (revertReason (E:=E) (Γ:=Γ) bytes) = some (.custom (errorData bytes)) := rfl

theorem require_decision {E : Env} {Γ : RCtx} (bytes : Roadmap.Bytes) :
    literalInput (requireFalse (E:=E) (Γ:=Γ) bytes) = some (.custom (errorData bytes)) := rfl

theorem assert_decision {E : Env} {Γ : RCtx} :
    literalInput (assertFalse (E:=E) (Γ:=Γ)) = some (panicInput .assert) := rfl

theorem bare_decision {E : Env} {Γ : RCtx} :
    literalInput (revertBare (E:=E) (Γ:=Γ)) = some .empty := rfl

theorem require_bare_decision {E : Env} {Γ : RCtx} :
    literalInput (requireBare (E:=E) (Γ:=Γ)) = some .empty := rfl

theorem empty_reason_not_bare : errorData [] ≠ ([] : Roadmap.Bytes) := by decide +kernel

theorem true_refused {E : Env} {Γ : RCtx} :
    literalInput (.builtin .assert (.cons (.bool true) .nil) rfl : RExpr E Γ (.tuple [])) = none ∧
    literalInput (.builtin .require (.cons (.bool true) .nil) rfl : RExpr E Γ (.tuple [])) = none := ⟨rfl,rfl⟩

/-- Actual effectful arguments are not evaluated by this syntactic compiler.
This is helper refusal, not a source-program rejection. -/
def effectful : RExpr E [.bool] (.tuple []) :=
  .builtin .require (.cons setFalse .nil) rfl

theorem effectful_refused : literalInput effectful = none := rfl

theorem effectful_source (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 9 effectful).run (locals,populated) =
      (.error (.revert []),(.cons (.bool false) .nil,populated)) := rfl

theorem reason_fits (bytes : Roadmap.Bytes) (small : bytes.length ≤ 33) :
    Failure.Fits 5 (errorData bytes) := by
  have padding : (32 - bytes.length % 32) % 32 < 32 := Nat.mod_lt _ (by decide +kernel)
  have extent : (errorData bytes).length ≤ 132 := by rw [reason_length]; omega
  have bound : 137 < Failure.wordLimit := by decide +kernel
  exact ⟨by omega, by omega, by omega⟩

/-- Inhabited compiler choice + actual Source execution + independent emitted
instruction execution, with nonempty old target stack/memory and ignored suffix.
No Source/byte-memory representation or runtime-memory encoder is assumed. -/
theorem reason_client (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (small : bytes.length ≤ 33) :
    ∃ program, emitLiteral 5 (revertReason (E:=E) (Γ:=[.bool]) bytes) = some program ∧
      (Source.evalE (global pipeline) frame 6 (revertReason bytes)).run (locals,populated) =
        (.error (.revert (errorData bytes)),(locals,populated)) ∧
      Failure.Slice.checkedRun (program ++ suffix) machine =
        some ({machine with memory := Failure.Slice.putBytes machine.memory 5 (errorData bytes)},
          some (.revert (errorData bytes))) :=
  literal_lowered (global pipeline) frame 0 locals populated (revertReason bytes)
    (.custom (errorData bytes)) (reason_decision bytes) 5 suffix machine
    (reason_fits bytes small) (by decide +kernel)

theorem retained_old_memory (bytes : Roadmap.Bytes) :
    Failure.Slice.putBytes machine.memory 5 (errorData bytes) 4 = 231 :=
  Failure.Slice.putBytes_frame machine.memory 5 4 (errorData bytes) (Or.inl (by decide +kernel))

theorem source_low_horizon (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) frame 2 (revertReason bytes)).run (locals,populated) =
      (.error .timeout,(locals,populated)) :=
  SourceFailures.reason_low_horizon (global pipeline) frame bytes locals populated

theorem panic_fits (code : PanicCode) : Failure.Fits 5 (panicData code) := by
  rw [Failure.Fits, panicData_length]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem panic_client (code : PanicCode) :
    Failure.Slice.checkedRun (Failure.emit 5 (panicInput code) ++ suffix) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory 5 (panicData code)},
        some (.revert (panicData code))) :=
  panic_checked code 5 suffix machine (panic_fits code) (by decide +kernel)

theorem wrong_panic_reason : panicData .assert ≠ errorData [] := by decide +kernel

theorem wrong_fit (bytes : Roadmap.Bytes) : ¬ Failure.Fits Failure.wordLimit bytes := by
  intro fit
  exact Nat.lt_irrefl _ fit.1

def tooHigh : Failure.Slice.Machine := { machine with stack := List.replicate 1025 ⟨77,by decide +kernel⟩ }
theorem stack_refusal : Failure.Slice.checkedRun (Failure.emit 5 .empty) tooHigh = none := by
  have height : tooHigh.stack.length = 1025 := by
    simp only [tooHigh, List.length_replicate]
  have invalid : decide (tooHigh.stack.length ≤ 1024) = false := by
    rw [height]
    rfl
  simp only [Failure.Slice.checkedRun, Failure.emit, Failure.Input.bytes, Failure.writes,
    List.nil_append, Failure.Slice.stackSafe, invalid, Bool.false_and]
  rfl

end Solidity.Lowering.V08.LiteralFailureControls
