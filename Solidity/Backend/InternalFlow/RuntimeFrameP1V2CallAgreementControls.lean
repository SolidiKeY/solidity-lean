import Solidity.Backend.InternalFlow.RuntimeFrameP1V2CallAgreement
import Solidity.Backend.InternalFlow.RuntimeFrameP1V2FramedRevertControls

/-! Regression: total captured-call agreement must have a real successful
compiler-selected call as well as the callee-OOB failure consumer. The empty
void call is selected by Mutation.compileCall on the SAME populated physical
caller fixture; arbitrary V2 journal/buffer and nonempty input stack remain. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1V2CallAgreementControls
open Evm Evm.Memory V3BareRevertProducer.Checks

/-- Ordinary empty-argument, empty-body void call; source success is intrinsic. -/
def statement : Stmt P.C P.Γ P.Γ :=
  .call "empty" (.nil : Args P.C P.Γ []) .none (.nil : Prog P.C [] [])

def compiled : Composition.Statement 0 F statement :=
  (Mutation.compileCall 0 F "empty" (.nil : Args P.C P.Γ []) .none
    (.nil : Prog P.C [] [])).get (by decide +kernel)

def selected : Composition.Program 0 F (.cons statement .nil) :=
  Composition.cons compiled (Composition.nil 0 compiled.checked.frag)

theorem metadata : selected.checked.need ≤ 8 ∧ selected.checked.allocates = false := by
  decide +kernel

theorem physical : V3BareRevertProducer.admitted selected 8 8
    1 16 caller P.base machine 10 :=
  fixture_input selected metadata.1 metadata.2

/-- Actual selected captured execution has the successful canonical prefix. -/
theorem target_success (journal : List CallRec) (buffer : List UInt8) :
    P1LangV2.targetSem (lift (NoneProducer.plan selected 8 8).code)
      (P1V2FramedRevertControls.input journal buffer) =
      ⟨[],some (.success [])⟩ := by
  rw [P1V2CallAgreement.agree selected 8 8 (NoneProducer.init_flags _ .refl)
    (P1V2FramedRevertControls.input journal buffer)
    (V3BareRevertProducer.coverage selected 8 8 1 16 caller P.base machine 10 physical)]
  rfl

/-- An always-revert replacement cannot satisfy this observation. -/
theorem not_always_revert (journal : List CallRec) (buffer : List UInt8) :
    P1LangV2.targetSem (lift (NoneProducer.plan selected 8 8).code)
      (P1V2FramedRevertControls.input journal buffer) ≠ ⟨[],some (.revert [])⟩ := by
  rw [target_success]
  intro same
  have final := congrArg Solidity.Roadmap.Prefix.final same
  cases final

end Solidity.Backend.InternalFlow.RuntimeFrame.P1V2CallAgreementControls
