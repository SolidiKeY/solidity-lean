import Solidity.Lowering.Readonly.ReceiverCapture
import Solidity.Lowering.Readonly.Controls
import Solidity.Backend.Passes.SourceCallControls

/-! Actual source receiver-before-arguments control. Declaration membership,
signature, target/value/arguments and capture execution are retained. No raw
callee outcome or runtime frame is manufactured by this argument-phase proof. -/
namespace Solidity.Lowering.Readonly.ReceiverControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Backend.Passes.SourceTypedCall
open Solidity.Backend.Passes.SourceCallControls (dCallOut)
open Solidity.Lowering.Readonly.Controls (Cell typedThree)

/-- `a` initially9 is evaluated as receiver before the argument sets `a=4`. -/
def target : RExpr EB [.address false] (.contract ⟨none, "C"⟩) :=
  .convExplicit (.local .here) (by decide)
def arguments : RConvArgs EB [.address false] [.address false] :=
  .cons (.assign (.local .here) (.addressLit [⟨4, by decide⟩])) (by decide) .nil

def before : Locals EB.layout [.address false] × St EB := (.cons (.address ext) .nil, sB)
def after : Locals EB.layout [.address false] × St EB := (.cons (.address (addr 4)) .nil, sB)
def captured : Captured EB [.address false] :=
  ⟨ext, word 0, .cons (.address (addr 4)) .nil,
    selOf "callOut(address)" ++ wordBytes (toWord 4)⟩

theorem signature : dCallOut.fnSig EB = some ([.address false], []) := by rfl

theorem actual_capture : CapturedAt (GB answerOnly) FC 6 target dCallOut signature (lit 0) arguments
    before after captured := by rfl

theorem source_resume :
    (evalE (GB answerOnly) FC 7 (.extCall target dCallOut signature (lit 0) arguments)).run before =
      (resume (GB answerOnly) FC 6 dCallOut [] captured).run after :=
  external_captured _ _ _ _ _ _ _ _ _ _ _ actual_capture

theorem receiver_not_self : captured.receiver ≠ FC.this := by decide +kernel

theorem receiver_not_retargeted : captured.receiver ≠ addr 4 := by decide +kernel

def caller : State Cell [.val .uint] :=
  (State.ofStorage typedThree).push (t := .val .uint) (ReceiverCapture.word (addr 4))

theorem actual_target_receiver :
    (ReceiverCapture.value captured.receiver).evalT caller = .ok (ReceiverCapture.word ext) :=
  ReceiverCapture.evaluate caller captured.receiver

theorem target_receiver_not_new_local :
    (ReceiverCapture.value captured.receiver).evalT caller ≠ .ok (ReceiverCapture.word (addr 4)) := by
  rw [ReceiverCapture.evaluate]
  intro same
  have addresses := ReceiverCapture.faithful (Except.ok.inj same)
  exact receiver_not_retargeted addresses

end Solidity.Lowering.Readonly.ReceiverControls
