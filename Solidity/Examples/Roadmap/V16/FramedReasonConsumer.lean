import Solidity.Backend.FailurePaths.FramedEmissionControls
import Solidity.Semantics.CtxEquiv.RevertFml

/-! Literal source Error(string) specification consumer. Actual compilation,
source failure, checked byte execution and numeric word-frame observations are
composed; no desired run/decoder theorem is assumed. Source state and numeric
word/byte frame are separate initial models, not a proved Source-to-physical
world map. This is not fetched EVM, gas, general runtime encoding or rollback
adequacy. The return signature and parameter count remain explicit. -/
namespace Solidity.Roadmap.V16.FramedReasonConsumer
open Solidity.Backend Source
open FailurePaths
open Solidity.Lowering.V08.SourceCustomErrorControls

abbrev Context : RCtx := [.bytes .memory]
def statement (reason : Roadmap.Bytes) : RStmt E Context false .body Context Context :=
  ReasonCodec.statement reason
def sourceStep (pipeline : Roadmap.Pipeline) (reason : Roadmap.Bytes) :
    Source.EM E [] (Source.Out E.layout Context Context) :=
  Source.execS (global pipeline) frame 7 0 none (statement reason) ParametricControls.locals
abbrev sourceInitial : Source.EMState E [] := (Source.L0 E,populated)
def image (reason : Roadmap.Bytes) : Backend.Program := Failure.emit 5 (.custom (Source.errorData reason))
def reached (reason : Roadmap.Bytes) : Failure.Slice.Machine :=
  {FramedEmissionControls.slice with memory := Failure.Slice.putBytes FramedEmissionControls.bytes 5 (Source.errorData reason)}

/-- Complete scoped result, not an assumed certificate or execution semantics. -/
def ResultSpec (pipeline : Roadmap.Pipeline) (reason : Roadmap.Bytes) : Prop :=
  Parametric.compile (global pipeline) 5 (statement reason) = some (image reason) ∧
  Source.Hoare (fun x => x=sourceInitial) (sourceStep pipeline reason)
    (fun _ _ => False)
    (fun halt output => halt=.revert (Source.errorData reason) ∧ output=sourceInitial) ∧
  Failure.Slice.checkedRun (image reason++Controls.tail) FramedEmissionControls.slice =
    some (reached reason,some (.revert (Source.errorData reason))) ∧
  MemoryOps.Physical.WordFrame FramedEmissionControls.numeric (reached reason).memory FramedEmissionControls.live ∧
  (reached reason).stack=FramedEmissionControls.slice.stack ∧
  Semantics.decodeError (Failure.Slice.getBytes (reached reason).memory 5 (Source.errorData reason).length)=some reason ∧
  DataPred.outcome (.error reason) (.revert (Source.errorData reason))

/-- Structural Hoare transport over an ABSTRACT operation prevents elaboration from running the concrete interpreter. The actual run is discharged by the producer below. -/
theorem of_failure_run :
    ∀ {E : Source.Env} {Γ : Source.RCtx} {α : Type} (operation : Source.EM E Γ α) (input output : Source.EMState E Γ) (halt : Source.Halt), operation.run input = (.error halt, output) → Source.Hoare (fun x => x=input) operation (fun _ _ => False) (fun h y => h=halt ∧ y=output) := by
  intro E Γ α operation input output halt execution x hx
  subst x
  rw [execution]
  exact ⟨rfl,rfl⟩

/-- Actual source and framed byte certificates construct every field; no successful run, codec or postcondition is assumed. The small bound discharges this published fixture's span/separation premises, not global admission. -/
theorem transport :
    ∀ (pipeline : Roadmap.Pipeline) (reason : Roadmap.Bytes), reason.length ≤ 33 → ResultSpec pipeline reason := by
  intro pipeline reason small
  have framed := FramedEmissionControls.reason_client pipeline reason small
  have actual := ReasonCodec.compiled_readback (R := Context) (global pipeline) frame 0 0 5 reason ParametricControls.locals populated Controls.tail FramedEmissionControls.slice (Lowering.V08.LiteralFailureControls.reason_fits reason small) (by decide)
  obtain ⟨last, run, wordFrame, saved, decoded⟩ := framed.2.2
  have same : last = reached reason := (Prod.mk.inj (Option.some.inj (run.symm.trans actual.2.2.1))).1
  have execution : (sourceStep pipeline reason).run sourceInitial = (.error (.revert (Source.errorData reason)), sourceInitial) := actual.2.1
  have spec := of_failure_run (sourceStep pipeline reason) sourceInitial sourceInitial (.revert (Source.errorData reason)) execution
  unfold ResultSpec
  constructor
  · exact actual.1
  constructor
  · exact spec
  constructor
  · exact actual.2.2.1
  constructor
  · rw [← same]
    exact wordFrame
  constructor
  · rfl
  constructor
  · dsimp only [reached]
    exact actual.2.2.2
  simp only [DataPred.outcome,DataPred.eval,Lowering.V08.errorData_transport_total,beq_self_eq_true]

/-- Actual empty, binary and33byte reasons, in either source pipeline. Empty reason still has an encoded Error payload. -/
theorem clients :
    ∀ (pipeline : Roadmap.Pipeline), ResultSpec pipeline [] ∧ ResultSpec pipeline [0,255,7] ∧ ResultSpec pipeline ReasonCodecControls.boundaryReason := by
  intro pipeline
  exact ⟨transport pipeline [] (by decide), transport pipeline [0,255,7] (by decide), transport pipeline ReasonCodecControls.boundaryReason (by decide)⟩

/-- The ACTUAL checked run cannot carry a different reason packet. -/
theorem wrong_payload :
    Failure.Slice.checkedRun (image [0,255,7] ++ Controls.tail) FramedEmissionControls.slice ≠ some (reached [0,255,7],some (.revert (Source.errorData [1,255,7]))) := by
  rw [(transport .legacy [0,255,7] (by decide)).2.2.1]
  intro same
  have observed := Option.some.inj ((Prod.mk.inj (Option.some.inj same)).2)
  have bad := Roadmap.Outcome.revert.inj observed
  exact (by decide : Source.errorData [0,255,7] ≠ Source.errorData [1,255,7]) bad

/-- Readback from the actual canonical reached memory cannot decode a different reason. -/
theorem wrong_readback :
    Semantics.decodeError (Failure.Slice.getBytes (reached [0,255,7]).memory 5 (Source.errorData [0,255,7]).length) ≠ some [1,255,7] := by
  rw [(transport .legacy [0,255,7] (by decide)).2.2.2.2.2.1]
  decide

/-- Error(empty string) is distinct from a bare empty revert. -/
theorem empty_reason_not_bare :
    ¬ DataPred.outcome (.bytes []) (.revert (Source.errorData [])) := by
  simp only [DataPred.outcome,DataPred.eval]
  decide

/-- The same source statement times out at zero horizon; no panic/revert completion or divergence is inferred. -/
theorem zero_fuel :
    ∀ (pipeline : Roadmap.Pipeline) (reason : Roadmap.Bytes), (Source.execS (global pipeline) frame 0 0 none (statement reason) ParametricControls.locals).run sourceInitial = (.error .timeout,sourceInitial) := by
  intro pipeline reason; rfl

/-- The COMPLETE32byte live word7 is retained in the reached target byte memory. -/
theorem protected_word :
    ∀ (_pipeline : Roadmap.Pipeline) (reason : Roadmap.Bytes), reason.length≤33 → Environment.readMemory (reached reason).memory 256 32 = Semantics.wordBytes 7 := by
  intro pipeline reason small
  have framed := (transport pipeline reason small).2.2.2.1
  obtain ⟨w,hw,hbytes⟩ := framed.cells 8 rfl
  change Evm.Word.val (Evm.wmod 7) = Evm.Word.val w at hw
  rw [← Evm.Word.val.inj hw] at hbytes
  exact hbytes

/-- Moving the actual payload readback window by one byte breaks the Error selector. -/
theorem wrong_window :
    Semantics.decodeError (Failure.Slice.getBytes (reached [0,255,7]).memory 6 (Source.errorData [0,255,7]).length) = none := by
  decide

/-- Actual REVERT cannot be relabelled RETURN even with identical bytes. -/
theorem wrong_success :
    Failure.Slice.checkedRun (image [0,255,7] ++ Controls.tail) FramedEmissionControls.slice ≠ some (reached [0,255,7],some (.success (Source.errorData [0,255,7]))) := by
  rw [(transport .legacy [0,255,7] (by decide)).2.2.1]
  intro same
  have bad := Option.some.inj ((Prod.mk.inj (Option.some.inj same)).2)
  cases bad

end Solidity.Roadmap.V16.FramedReasonConsumer


/-- info: 'Solidity.Roadmap.V16.FramedReasonConsumer.of_failure_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.FramedReasonConsumer.of_failure_run

/-- info: 'Solidity.Roadmap.V16.FramedReasonConsumer.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.FramedReasonConsumer.transport

/-- info: 'Solidity.Roadmap.V16.FramedReasonConsumer.clients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.FramedReasonConsumer.clients

/-- info: 'Solidity.Roadmap.V16.FramedReasonConsumer.wrong_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.FramedReasonConsumer.wrong_payload

/-- info: 'Solidity.Roadmap.V16.FramedReasonConsumer.wrong_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.FramedReasonConsumer.wrong_readback

/-- info: 'Solidity.Roadmap.V16.FramedReasonConsumer.empty_reason_not_bare' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.FramedReasonConsumer.empty_reason_not_bare

/-- info: 'Solidity.Roadmap.V16.FramedReasonConsumer.zero_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.FramedReasonConsumer.zero_fuel

/-- info: 'Solidity.Roadmap.V16.FramedReasonConsumer.protected_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.FramedReasonConsumer.protected_word

/-- info: 'Solidity.Roadmap.V16.FramedReasonConsumer.wrong_window' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.FramedReasonConsumer.wrong_window

/-- info: 'Solidity.Roadmap.V16.FramedReasonConsumer.wrong_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.FramedReasonConsumer.wrong_success
