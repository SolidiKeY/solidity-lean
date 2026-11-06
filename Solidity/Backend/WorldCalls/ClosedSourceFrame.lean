import Solidity.Lowering.Readonly.SourceAllHistories
import Solidity.Backend.WorldCalls.SourceBridge

/-! Closed same-invocation SOURCE P2 facts for the actual pre-decoder run.
Local capture is retained. Whole-body/original-site embedding, Source-to-Core
representation and actual native/target execution remain separate obligations. -/
namespace Solidity.Backend.WorldCalls.ClosedSourceFrame
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
theorem history_of_raw (i : InvocationFrame.Invocation E Γ dn ps rs)
    (raw : Except Halt Outcome) (final : St E) (actual : i.RawAt raw final) :
    StaticJournal.History i.after.2.ex i.mode final.ex := by
  have history := (SourceHistory.all_at i.global i.horizon).callAddr i.frame
    i.captured.receiver i.captured.value i.captured.input i.requested (L0 E) i.after.2
  change (callAddr i.global i.frame i.horizon i.captured.receiver i.captured.value
    i.captured.input i.requested).run (L0 E,i.after.2) = (raw,(L0 E,final)) at actual
  rw [actual] at history
  exact history

theorem frames_of_raw (i : InvocationFrame.Invocation E Γ dn ps rs)
    (raw : Except Halt Outcome) (final : St E) (actual : i.RawAt raw final)
    (static : i.mode = true) : i.RuntimeFrames final :=
  ⟨static, history_of_raw i raw final actual⟩

theorem evaluated_frame (i : InvocationFrame.Invocation E Γ dn ps rs)
    (static : i.mode = true) :
    i.RawAt (SourceBridge.evaluated i).1 (SourceBridge.evaluated i).2 ∧
      i.RuntimeFrames (SourceBridge.evaluated i).2 :=
  ⟨SourceBridge.evaluated_raw i, frames_of_raw i _ _ (SourceBridge.evaluated_raw i) static⟩

theorem caller_storage (i : InvocationFrame.Invocation E Γ dn ps rs)
    (raw : Except Halt Outcome) (final : St E) (actual : i.RawAt raw final)
    (static : i.mode = true) :
    (final.ex.world.accounts i.frame.this).storage =
      (i.after.2.ex.world.accounts i.frame.this).storage :=
  (history_of_raw i raw final actual).storage static i.frame.this
end Solidity.Backend.WorldCalls.ClosedSourceFrame
