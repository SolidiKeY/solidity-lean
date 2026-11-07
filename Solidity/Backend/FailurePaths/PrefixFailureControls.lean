import Solidity.Backend.FailurePaths.PrefixFailure
import Solidity.Backend.FailurePaths.EncodedErrorControls

/-! Real public writer prefixes inhabit the nonhalting-prefix consumer in
both pipelines. Early terminals, unsupported opcodes and swapped stack words
remain refusals. This supplies no general runtime encoder/compiler instance. -/
namespace Solidity.Backend.FailurePaths.PrefixFailure.Controls
open Source Failure.Slice
open Lowering.V08.SourceCustomErrorControls

def entry := FramedEmissionControls.slice
def suffix : Backend.Program := [.op .ADD]

theorem joint (pipeline : Roadmap.Pipeline) (value : Bool) :
    (execS (global pipeline) frame 3 0 none EncodedError.Controls.statement
      (EncodedError.Controls.caller value)).run (Source.L0 E,populated) =
      (.error (.revert (EncodedError.Controls.packet pipeline value)),(Source.L0 E,populated)) ∧
    checkedRun (writer 5 (EncodedError.Controls.packet pipeline value) ++ (.op .REVERT :: suffix)) entry =
      some ({entry with memory:=putBytes entry.memory 5 (EncodedError.Controls.packet pipeline value)},
        some (.revert (EncodedError.Controls.packet pipeline value))) := by
  exact source_writer (E:=E) (Γ:=[.bool]) (τ:=.bool) (R:=[]) (global pipeline) frame 0 0 5
    EncodedError.Controls.error EncodedError.Controls.typed .here rfl
    (EncodedError.Controls.caller value) populated populated
    (EncodedError.Controls.data value) (EncodedError.Controls.encoding value populated)
    entry suffix (EncodedError.Controls.fits pipeline value) (by decide)

theorem public_code (pipeline : Roadmap.Pipeline) (value : Bool) :
    writer 5 (EncodedError.Controls.packet pipeline value) ++ [.op .REVERT] =
      Failure.emit 5 (.custom (EncodedError.Controls.packet pipeline value)) :=
  public_emitter 5 _

theorem final_frame (pipeline : Roadmap.Pipeline) (value : Bool) :
    MemoryOps.Physical.WordFrame FramedEmissionControls.numeric
      (putBytes entry.memory 5 (EncodedError.Controls.packet pipeline value)) FramedEmissionControls.live := by
  apply FramedEmission.preserve_bytes FramedEmissionControls.initial
  intro c hc
  subst c
  left
  rw [EncodedError.Controls.packet_length]
  decide

theorem saved_tail : entry.stack = [⟨77,by decide⟩] := rfl

def early : Backend.Program := Failure.emit 0 .empty

theorem early_run : checkedRun early entry = some (entry,some (.revert [])) := by
  exact Failure.checkedRun_emit_suffix 0 .empty [] entry
    ⟨by decide,by decide,by decide⟩ (by decide)

theorem early_not_prefix (ready : Machine) :
    checkedRun early entry ≠ some (ready,none) := by
  intro observed
  rw [early_run] at observed
  cases observed

theorem unsupported_refused : checkedRun [.op .ADD] entry = none := rfl

theorem swapped_operands_refused (pipeline : Roadmap.Pipeline) (value : Bool) :
    (prepared entry 5 (EncodedError.Controls.packet pipeline value)
      (EncodedError.Controls.fits pipeline value)).stack ≠
    ⟨(EncodedError.Controls.packet pipeline value).length,(EncodedError.Controls.fits pipeline value).2.1⟩ ::
      ⟨5,(EncodedError.Controls.fits pipeline value).1⟩ :: entry.stack := by
  exact swapped_layout_refused entry 5 _ (EncodedError.Controls.fits pipeline value)
    (by rw [EncodedError.Controls.packet_length];decide)

theorem compiler_refusal_retained (pipeline : Roadmap.Pipeline) :
    compileStatement (global pipeline) 5 EncodedError.Controls.statement = none :=
  EncodedError.Controls.old_selector_refuses pipeline

theorem timeout_retained (pipeline : Roadmap.Pipeline) (value : Bool) (payload : Roadmap.Bytes) :
    (execS (global pipeline) frame 1 0 none EncodedError.Controls.statement
      (EncodedError.Controls.caller value)).run (Source.L0 E,populated) ≠
      (.error (.revert payload),(Source.L0 E,populated)) :=
  EncodedError.Controls.timeout_not_revert pipeline value payload

/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.Controls.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.Controls.public_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_code
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.Controls.final_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms final_frame
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.Controls.saved_tail' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms saved_tail
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.Controls.early_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms early_run
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.Controls.early_not_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms early_not_prefix
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.Controls.unsupported_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms unsupported_refused
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.Controls.swapped_operands_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms swapped_operands_refused
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.Controls.compiler_refusal_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiler_refusal_retained
/-- info: 'Solidity.Backend.FailurePaths.PrefixFailure.Controls.timeout_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms timeout_retained
end Solidity.Backend.FailurePaths.PrefixFailure.Controls
