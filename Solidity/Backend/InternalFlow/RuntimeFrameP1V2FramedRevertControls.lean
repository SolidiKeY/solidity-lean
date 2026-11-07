import Solidity.Backend.InternalFlow.RuntimeFrameP1V2FramedRevert

/-! Regression: a frame-free V2 revert must not replace the actual captured
callee-OOB execution. This importing consumer retains the physical Entry,
selected Mutation.compileCall image, source write-before-OOB and nonempty saved
stack, while allowing every preexisting V2 journal and return buffer. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2FramedRevertControls
open Evm Evm.Memory

/-- Same typed caller/frame/cursor as the actual selected callee-OOB fixture.
V2-only state is arbitrary and does not discharge a physical premise. -/
def input (journal : List CallRec) (buffer : List UInt8) : P1LangV2.Input V3BareRevertProducer.Checks.P.C V3BareRevertProducer.Checks.P.Γ :=
  ⟨1,16,V3BareRevertProducer.Checks.caller,V3BareRevertProducer.Checks.P.base,
    {base := V3BareRevertProducer.Checks.machine, calls := journal, returndata := buffer},10⟩

theorem physical_entry (journal : List CallRec) (buffer : List UInt8) :
    InterfaceV1.Entry (V3BareRevertProducer.plan V3BareRevertProducer.Checks.callSelected 8 8)
      1 0 16 V3BareRevertProducer.Checks.F V3BareRevertProducer.Checks.caller V3BareRevertProducer.Checks.P.base (input journal buffer).machine.base 10 :=
  V3BareRevertProducer.coverage V3BareRevertProducer.Checks.callSelected 8 8 1 16 V3BareRevertProducer.Checks.caller
    V3BareRevertProducer.Checks.P.base V3BareRevertProducer.Checks.machine 10 V3BareRevertProducer.Checks.call_input

/-- The body writes its existing aliased object before the reached OOB failure;
the selected captured call, rather than an assumed target run, supplies V2 failure. -/
theorem selected_call_reverts (journal : List CallRec) (buffer : List UInt8) :
    runV2 (lift (V3BareRevertProducer.plan V3BareRevertProducer.Checks.callSelected 8 8).code)
      (input journal buffer).machine = .revert journal [] :=
  P1V2FramedRevert.run_revert V3BareRevertProducer.Checks.callSelected 8 8 (input journal buffer)
    (physical_entry journal buffer) V3BareRevertProducer.Checks.call_source

theorem same_observation (journal : List CallRec) (buffer : List UInt8) :
    P1LangV2.targetSem (lift (V3BareRevertProducer.plan V3BareRevertProducer.Checks.callSelected 8 8).code)
      (input journal buffer) = P1LangV2.sourcePrefix (V3BareRevertProducer.Checks.call.run V3BareRevertProducer.Checks.caller) :=
  P1V2FramedRevert.prefix_revert V3BareRevertProducer.Checks.callSelected 8 8 (input journal buffer)
    (physical_entry journal buffer) V3BareRevertProducer.Checks.call_source

/-- Arbitrary V2 metadata cannot repair the wrong physical cursor. -/
theorem wrong_cursor (journal : List CallRec) (buffer : List UInt8) :
    ¬ V3BareRevertProducer.admitted V3BareRevertProducer.Checks.callSelected 8 8
      1 16 V3BareRevertProducer.Checks.caller V3BareRevertProducer.Checks.P.base (input journal buffer).machine.base 11 :=
  V3BareRevertProducer.Checks.wrong_cursor

/-- This failure cannot be relabelled as a payload-bearing revert. -/
theorem nonempty_payload_refused (journal : List CallRec) (buffer data : List UInt8)
    (nonempty : data ≠ []) :
    runV2 (lift (V3BareRevertProducer.plan V3BareRevertProducer.Checks.callSelected 8 8).code)
      (input journal buffer).machine ≠ .revert journal data := by
  rw [selected_call_reverts]
  intro same
  cases same
  exact nonempty rfl

/-- The reached input is populated, including a nonempty saved caller stack. -/
theorem saved_tail (journal : List CallRec) (buffer : List UInt8) :
    (input journal buffer).machine.base.stack = [w[77]] := rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2FramedRevertControls
