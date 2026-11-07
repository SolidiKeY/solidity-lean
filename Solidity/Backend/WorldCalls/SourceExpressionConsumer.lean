import Solidity.Backend.WorldCalls.ClosedSourceFrame
import Solidity.Lowering.Readonly.SourcePayloadDecodeEffects
import Solidity.Source.Hoare

/-! The actual resolved external expression after its captured argument effects.
Source-only: no whole-body embedding, Core or compiler-target adequacy follows. -/
namespace Solidity.Backend.WorldCalls.SourceExpressionConsumer
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceTypedCall
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}

/-- Capture is evaluated once at the original expression's horizon and position.
The remaining run includes the real call and caller-side declared-return decoder. -/
theorem after_capture (i : InvocationFrame.Invocation E Γ dn ps rs) :
    (evalE i.global i.frame (i.horizon+1)
      (.extCall i.target i.declaration i.signature i.value i.arguments)).run i.before =
    (resume (Γ := Γ) i.global i.frame i.horizon i.declaration rs i.captured).run i.after := by
  have captured :
      (capture i.global i.frame i.horizon i.target i.declaration i.value i.arguments).run i.before =
        (.ok i.captured, i.after) := i.execution
  simp only [eval_external, Hoare.run_bind, captured]

/-- No successful return or decode premise: halts and caller-decoding failures
keep the reached state, with persistent storage protected in static mode. -/
theorem resume_history (i : InvocationFrame.Invocation E Γ dn ps rs) :
    SourceHistory.Effect i.mode
      (resume (Γ := Γ) i.global i.frame i.horizon i.declaration rs i.captured) :=
  SourceHistory.Effect.bind i.mode _ _
    (SourceHistory.Effect.sub i.mode (L0 E) _
      ((SourceDispatchV2.all_at i.global i.horizon).callAddr i.frame
        i.captured.receiver i.captured.value i.captured.input i.requested))
    (fun pair => SourceHistory.extReturn_effect i.mode rs pair.1)

theorem expression_history (i : InvocationFrame.Invocation E Γ dn ps rs) :
    StaticJournal.History i.after.2.ex i.mode
      ((evalE i.global i.frame (i.horizon+1)
        (.extCall i.target i.declaration i.signature i.value i.arguments)).run i.before).2.2.ex := by
  simpa only [after_capture] using resume_history i i.after.1 i.after.2

/-- The checkpoint is AFTER capture; earlier argument writes are not undone or
forbidden merely because the selected callee is view/pure. -/
theorem storage (i : InvocationFrame.Invocation E Γ dn ps rs) (mode : i.mode = true) :
    (((evalE i.global i.frame (i.horizon+1)
      (.extCall i.target i.declaration i.signature i.value i.arguments)).run i.before).2.2.ex.world.accounts
        i.frame.this).storage =
      (i.after.2.ex.world.accounts i.frame.this).storage :=
  (expression_history i).storage mode i.frame.this
end Solidity.Backend.WorldCalls.SourceExpressionConsumer
