import Solidity.Backend.WorldCalls.ClosedSourceConsumers
import Solidity.Backend.WorldCalls.SourceBridgeControls

/-! Inhabited restricted paired payment client and actual read-only reentry.
No general target callback implementation is asserted. -/
namespace Solidity.Backend.WorldCalls.ClosedConsumerControls
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
open PaymentControl
def boundary : Premises origin := ClosedSourceConsumers.premises origin code Observed Step
  premises.bound premises.execution premises.observed
  (fun key initial raw final target step =>
    (SourceBridge.raw_iff origin raw final).mpr (premises.sourceRaw key initial raw final target step))

theorem inhabited : boundary.Step (identity origin) initial (.ok (.success [])) sourceFinal (.ok final 0) :=
  PaymentControl.inhabited

theorem consumer :
    Evm.run boundary.code.full initial = .ok final 0 ∧ origin.RawAt (.ok (.success [])) sourceFinal :=
  ⟨(Callbacks.returned boundary _ _ _ _ _ inhabited).2.1,
    (Callbacks.returned boundary _ _ _ _ _ inhabited).2.2.2⟩

theorem unrelated_bytes_refused :
    ¬ boundary.Step (identity origin) initial (.ok (.success [1])) sourceFinal (.ok final 0) :=
  PaymentControl.unrelated_raw_refused

theorem read_only_reentry :
    (Controls.readFinal.ex.world.accounts Controls.readOrigin.frame.this).storage =
      (Controls.readOrigin.after.2.ex.world.accounts Controls.readOrigin.frame.this).storage :=
  ClosedSourceFrame.caller_storage Controls.readOrigin _ _ Controls.read_reentry_raw rfl

theorem typed_projection (typed : Solidity.Storage Controls.Cell)
    (exit : Controls.representation.relates
      (Controls.final.ex.world.accounts Controls.origin.frame.this).storage typed) :
    typed = Controls.typedThree :=
  ClosedSourceConsumers.typed_storage Controls.origin _ _ Controls.raw rfl
    Controls.representation Controls.typedThree typed
    Controls.entry_representation exit
end Solidity.Backend.WorldCalls.ClosedConsumerControls
