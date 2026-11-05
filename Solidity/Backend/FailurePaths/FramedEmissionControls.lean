import Solidity.Backend.FailurePaths.FramedEmission
import Solidity.Backend.FailurePaths.ReasonCodecControls
import Solidity.Backend.FailurePaths.BooleanReturn

/-! Inhabited physical frames, actual source reason failures in both pipelines,
boundary-adjacent emissions and an overlap counterexample. No full world/frame
or bytecode adequacy is inferred from the component relations. -/
namespace Solidity.Backend.FailurePaths.FramedEmissionControls
open Source MemoryOps.Physical
open Lowering.V08.SourceCustomErrorControls

def numeric : Evm.Machine := Evm.Memory.writeMachine {Evm.Machine.init with stack := [.val (Evm.wmod 77)]} 8 (.val (Evm.wmod 7))
def bytes : Environment.Memory := Environment.writeBytes (fun _ => 0) 256 (Semantics.wordBytes 7)
def live (c : Nat) := c=8
def slice : Failure.Slice.Machine := ⟨[⟨77,by decide⟩],bytes⟩

theorem initial : WordFrame numeric bytes live := by
  have empty : WordFrame ({Evm.Machine.init with stack := [.val (Evm.wmod 77)]})
      (fun _ => 0) (fun _ => False) := ⟨fun _ h => h.elim,fun _ h => h.elim⟩
  have written := empty.write 8 (Evm.wmod 7) (by decide)
  exact ⟨fun c hc => written.fits c (Or.inr hc),fun c hc => written.cells c (Or.inr hc)⟩

theorem reason_client (pipeline : Roadmap.Pipeline) (reason : Roadmap.Bytes) (small : reason.length≤33) :
    Parametric.compile (global pipeline) 5
      (ReasonCodec.statement (E:=E) (R:=[.bytes .memory]) (Γ:=[.bytes .memory]) reason) =
      some (Failure.emit 5 (.custom (Source.errorData reason))) ∧
    Parametric.Reverts (global pipeline) frame 7 0 (ReasonCodec.statement (R:=[.bytes .memory]) reason)
      ParametricControls.locals populated (Source.errorData reason) ∧
    ∃ reached,
      Failure.Slice.checkedRun (Failure.emit 5 (.custom (Source.errorData reason)) ++ Controls.tail) slice =
        some (reached,some (.revert (Source.errorData reason))) ∧
      WordFrame numeric reached.memory live ∧ reached.stack=slice.stack ∧
      Semantics.decodeError (Failure.Slice.getBytes reached.memory 5 (Source.errorData reason).length) = some reason := by
  apply FramedEmission.compiled_reason (global pipeline) frame 0 0 5 reason ParametricControls.locals populated
    Controls.tail slice numeric live initial (Lowering.V08.LiteralFailureControls.reason_fits reason small) (by decide)
  intro c hc
  subst c
  left
  have padding : (32-reason.length%32)%32<32 := Nat.mod_lt _ (by decide)
  rw [Lowering.V08.LiteralFailureLowering.reason_length]
  omega

/-- Payload writes ending at the word's first byte, or beginning just after
its last byte, preserve the entire live word and the nonempty saved stack. -/
theorem boundary_emission (after : Bool) (suffix : Backend.Program) :
    ∃ reached,
      Failure.Slice.checkedRun (Failure.emit (if after then 288 else 254) (.custom [255,1]) ++ suffix) slice =
        some (reached,some (.revert [255,1])) ∧
      WordFrame numeric reached.memory live ∧ reached.stack=slice.stack := by
  apply FramedEmission.emitter slice initial (if after then 288 else 254) (.custom [255,1]) suffix
    (by cases after <;> unfold Failure.Fits <;> decide) (by decide)
  intro c hc
  subst c
  cases after <;> decide

/-- Overlap is not silently accepted: the live word7 loses its low byte when
the actual emitter writes zero at byte287. The checked emitter still reverts. -/
theorem overlap_refused :
    Failure.Slice.checkedRun (Failure.emit 287 (.custom [0])) slice =
      some ({slice with memory := Failure.Slice.putBytes bytes 287 [0]},some (.revert [0])) ∧
    ¬ WordFrame numeric (Failure.Slice.putBytes bytes 287 [0]) live := by
  constructor
  · exact Failure.checkedRun_emit_suffix 287 (.custom [0]) [] slice (by unfold Failure.Fits;decide) (by decide)
  · intro wrong
    obtain ⟨w,hw,hbytes⟩ := wrong.cells 8 rfl
    change Evm.Word.val (Evm.wmod 7)=Evm.Word.val w at hw
    rw [←Evm.Word.val.inj hw] at hbytes
    have last := congrArg (fun bs : List UInt8 => bs[31]?) hbytes
    have dirty : (Environment.readMemory (Failure.Slice.putBytes bytes 287 [0]) (32*8) 32)[31]?=some 0 := by decide
    have original : (Semantics.wordBytes (Evm.wmod 7).val)[31]?=some 7 := by decide
    change (Environment.readMemory (Failure.Slice.putBytes bytes 287 [0]) (32*8) 32)[31]?=
      (Semantics.wordBytes (Evm.wmod 7).val)[31]? at last
    rw [dirty,original] at last
    exact (by decide : (some (0:UInt8))≠some 7) last

/-- The existing literal Boolean return selector, actual hidden-slot overwrite,
return extraction/encoding and successful byte-emitter frame are all exercised. -/
theorem boolean_return (pipeline : Roadmap.Pipeline) (old value : Bool) :
    BooleanReturn.compile 5 (BooleanReturn.statement (E:=E) (Γ:=[.bool]) value) =
      some (Failure.emit 5 (.returned (BooleanReturn.payload value))) ∧
    (Source.execS (global pipeline) frame 7 0 none (BooleanReturn.statement value) (BooleanReturn.locals old)).run
      (Source.L0 E,populated) = (.ok (.ret (BooleanReturn.locals value)),(Source.L0 E,populated)) ∧
    Source.retVals (BooleanReturn.locals (E:=E) value) 0 [.bool] = .ok (BooleanReturn.values value) ∧
    (Source.encodeVals frame 0 false (BooleanReturn.values value) : Source.EM E [] _).run
      (Source.L0 E,populated) = (.ok (BooleanReturn.payload value),(Source.L0 E,populated)) ∧
    ∃ reached,
      Failure.Slice.checkedRun (Failure.emit 5 (.returned (BooleanReturn.payload value)) ++ Controls.tail) slice =
        some (reached,some (.success (BooleanReturn.payload value))) ∧
      WordFrame numeric reached.memory live ∧ reached.stack=slice.stack := by
  refine ⟨rfl,BooleanReturn.source_run (global pipeline) frame 0 old value populated,
    BooleanReturn.returned_values value,BooleanReturn.encoded_values frame 0 value populated,?_⟩
  apply FramedEmission.emitter slice initial 5 (.returned (BooleanReturn.payload value)) Controls.tail
    (by cases value <;> unfold Failure.Fits <;> decide) (by decide)
  intro c hc
  subst c
  cases value <;> decide

#print axioms initial
#print axioms reason_client
#print axioms boundary_emission
#print axioms overlap_refused
#print axioms boolean_return
end Solidity.Backend.FailurePaths.FramedEmissionControls
