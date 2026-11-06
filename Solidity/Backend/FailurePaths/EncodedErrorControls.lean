import Solidity.Backend.FailurePaths.EncodedError
import Solidity.Backend.FailurePaths.FramedEmissionControls
import Solidity.Backend.FailurePaths.TransientControls
import Solidity.Lowering.V08.BoolErrorControls

/-! Inhabited encoder-premise consumers for a local Boolean custom-error
argument. Both pipelines use the actual encoder and populated Source state.
No general encoder, P7 payload transport or full EVM instance is fabricated. -/
namespace Solidity.Backend.FailurePaths.EncodedError.Controls
open Source
open Lowering.V08.SourceCustomErrorControls

def error : Source.Decl := Lowering.V08.BoolErrorControls.declaration 1
theorem typed : error.paramTys E = some [.bool] := rfl

def caller (value : Bool) : Source.Locals E.layout [.bool] := .cons (.bool value) .nil
def statement : RStmt E [] false .body [.bool] [.bool] :=
  EncodedError.statement error typed .here rfl
def data (value : Bool) : Roadmap.Bytes := Lowering.V08.BoolErrorLowering.encoded [value]
def packet (pipeline : Roadmap.Pipeline) (value : Bool) : Roadmap.Bytes :=
  EncodedError.packet (τ:=.bool) (global pipeline) error (data value)

theorem encoding (value : Bool) (state : St E) :
    Premises.EncodingAt frame 2
      (EncodedError.values ((caller value).get .here)).toR state state (data value) :=
  boolean_encoding frame 2 [value] state

theorem packet_length (pipeline : Roadmap.Pipeline) (value : Bool) :
    (packet pipeline value).length=36 := by
  change (Lowering.V08.BoolErrorLowering.payload (global pipeline) error [value]).length=36
  exact Lowering.V08.BoolErrorLowering.payload_length (global pipeline) error [value]

theorem fits (pipeline : Roadmap.Pipeline) (value : Bool) :
    Failure.Fits 5 (packet pipeline value) := by
  unfold Failure.Fits
  rw [packet_length]
  exact ⟨by decide,by decide,by decide⟩

theorem joint (pipeline : Roadmap.Pipeline) (value : Bool) :
    (execS (global pipeline) frame 3 0 none statement (caller value)).run (Source.L0 E,populated) =
      (.error (.revert (packet pipeline value)),(Source.L0 E,populated)) ∧
    ∃ reached,
      Failure.Slice.checkedRun
        (Failure.emit 5 (.custom (packet pipeline value)) ++ Lowering.V08.BoolErrorControls.suffix)
        FramedEmissionControls.slice =
        some (reached,some (.revert (packet pipeline value))) ∧
      MemoryOps.Physical.WordFrame FramedEmissionControls.numeric reached.memory FramedEmissionControls.live ∧
      reached.stack=FramedEmissionControls.slice.stack ∧
      Failure.Slice.getBytes reached.memory 5 (packet pipeline value).length=packet pipeline value := by
  apply EncodedError.emitted_frame (R:=[]) (global pipeline) frame 0 0 5 error typed .here rfl
    (caller value) populated populated (data value) (encoding value populated)
    FramedEmissionControls.slice FramedEmissionControls.numeric FramedEmissionControls.live
    FramedEmissionControls.initial Lowering.V08.BoolErrorControls.suffix (fits pipeline value) (by decide)
  intro c hc
  subst c
  left
  rw [show (EncodedError.packet (τ:=.bool) (global pipeline) error (data value)).length=36
    from packet_length pipeline value]
  decide

theorem different_payloads (pipeline : Roadmap.Pipeline) :
    packet pipeline true ≠ packet pipeline false := by
  intro same
  change (global pipeline).selector (sigOf E.layout error.name [.bool]) ++ data true =
    (global pipeline).selector (sigOf E.layout error.name [.bool]) ++ data false at same
  have different : data true ≠ data false := by decide
  exact different (List.append_cancel_left same)

theorem old_selector_refuses (pipeline : Roadmap.Pipeline) :
    compileStatement (global pipeline) 5 statement=none := rfl

theorem argument_incomplete (pipeline : Roadmap.Pipeline) (value : Bool) :
    Premises.IncompleteAt
      (evalConvArgs (global pipeline) frame 0 (EncodedError.arguments (E:=E) .here rfl))
      (caller value,populated) (caller value,populated) := rfl

theorem argument_timeout (pipeline : Roadmap.Pipeline) (value : Bool) :
    (execS (global pipeline) frame 1 0 none statement (caller value)).run (Source.L0 E,populated) =
      (.error .timeout,(Source.L0 E,populated)) :=
  EncodedError.arguments_incomplete (R:=[]) (global pipeline) frame 0 0 error typed
    (EncodedError.arguments .here rfl) (caller value) (caller value) populated populated
    (argument_incomplete pipeline value)

theorem zero_horizon (pipeline : Roadmap.Pipeline) (value : Bool) :
    (execS (global pipeline) frame 0 0 none statement (caller value)).run (Source.L0 E,populated) =
      (.error .timeout,(Source.L0 E,populated)) := rfl

def dirty : St E := {populated with ex:=populated.ex.run FailurePaths.Controls.ops}

theorem world_client (pipeline : Roadmap.Pipeline) (value : Bool) :
    (execS (global pipeline) frame 3 0 none statement (caller value)).run (Source.L0 E,dirty) =
      (.error (.revert (packet pipeline value)),(Source.L0 E,dirty)) ∧
    (populated.ex.enter frame.this frame.sender frame.value frame.cd frame.static).rollback dirty.ex=populated.ex ∧
    Failure.Local.execute
      (Failure.Local.save (MemoryOps.Physical.worldJournal populated.ex FramedEmissionControls.slice))
      5 (.custom (packet pipeline value))
      (MemoryOps.Physical.worldJournal dirty.ex FramedEmissionControls.slice) =
      some (MemoryOps.Physical.worldJournal populated.ex FramedEmissionControls.slice,.revert (packet pipeline value)) :=
  EncodedError.world_unwind (R:=[]) (global pipeline) frame 0 0 5 error typed .here rfl
    (caller value) dirty dirty populated (data value) (encoding value dirty)
    FailurePaths.Controls.ops rfl FramedEmissionControls.slice FramedEmissionControls.slice
    (fits pipeline value) (by decide)

theorem p7_nonempty_still_refused (bytes : Failure.Slice.Machine) (cells : List Nat) :
    ¬ Premises.TransientPayloadAt Transient.Controls.frame (Failure.emit 0 (.custom [1]))
      Transient.Controls.target bytes cells 0 [1] :=
  TransientControls.no_current_payload_transport bytes cells

theorem wrong_encoding_refused (value : Bool) :
    ¬ Premises.EncodingAt frame 2
      (EncodedError.values ((caller value).get .here)).toR populated populated (data (!value)) := by
  intro assumed
  have actual := encoding value populated
  have equal := congrArg Prod.fst (actual.symm.trans assumed)
  have different : data value ≠ data (!value) := by cases value <;> decide
  exact different (Except.ok.inj equal)

theorem timeout_not_revert (pipeline : Roadmap.Pipeline) (value : Bool) (payload : Roadmap.Bytes) :
    (execS (global pipeline) frame 1 0 none statement (caller value)).run (Source.L0 E,populated) ≠
      (.error (.revert payload),(Source.L0 E,populated)) := by
  intro observed
  rw [argument_timeout] at observed
  cases observed

/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.wrong_encoding_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_encoding_refused
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.timeout_not_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_not_revert

/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoding
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.packet_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packet_length
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fits
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms joint
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.different_payloads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms different_payloads
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.old_selector_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms old_selector_refuses
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.argument_incomplete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms argument_incomplete
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.argument_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms argument_timeout
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_horizon
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.world_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms world_client
/-- info: 'Solidity.Backend.FailurePaths.EncodedError.Controls.p7_nonempty_still_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms p7_nonempty_still_refused
end Solidity.Backend.FailurePaths.EncodedError.Controls
