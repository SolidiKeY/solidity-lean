import Solidity.Backend.WorldCalls.SourceBridge
import Solidity.Backend.WorldCalls.PaymentControl
import Solidity.Lowering.Readonly.Controls

/-! Actual nonself source runs and a restricted paired payment target client.
No general target callback/raw-byte/ABI producer is supplied by these controls. -/
namespace Solidity.Backend.WorldCalls.SourceBridgeControls
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
open SourceBridge
namespace R
abbrev origin := Controls.origin
abbrev final := Controls.final
end R

theorem nonself_raw :
    (Solidity.Lowering.V08.SourceCallPhase.raw R.origin.global R.origin.frame R.origin.horizon (request R.origin)).run R.origin.after =
      (.ok (.success [7]), (R.origin.after.1, R.final)) :=
  (raw_iff R.origin _ _).mpr Controls.raw

theorem captured_bytes :
    (Solidity.Lowering.V08.SourceCallPhase.capture R.origin.global R.origin.frame R.origin.horizon (request R.origin)).run R.origin.after =
      (.ok (.success [7], R.final), (R.origin.after.1, R.final)) := captured R.origin _ _ nonself_raw

theorem wrong_bytes_refused : ¬
    (Solidity.Lowering.V08.SourceCallPhase.raw R.origin.global R.origin.frame R.origin.horizon (request R.origin)).run R.origin.after =
      (.ok (.success [9]), (R.origin.after.1, R.final)) := by
  intro bad
  exact Controls.wrong_raw_rejected ((raw_iff R.origin _ _).mp bad)

theorem reentry_raw :
    (Solidity.Lowering.V08.SourceCallPhase.raw Controls.readOrigin.global Controls.readOrigin.frame Controls.readOrigin.horizon
      (request Controls.readOrigin)).run Controls.readOrigin.after =
      (.ok (.success []), (Controls.readOrigin.after.1, Controls.readFinal)) :=
  (raw_iff Controls.readOrigin _ _).mpr Controls.read_reentry_raw

/-- This fixture supplies its actual source history; it does not prove all histories. -/
theorem reentry_frame :
    (Controls.readFinal.ex.world.accounts Controls.readOrigin.frame.this).storage =
      (Controls.readOrigin.after.2.ex.world.accounts Controls.readOrigin.frame.this).storage :=
  Controls.readOrigin.storage _ _ ((raw_iff _ _ _).mp reentry_raw) Controls.read_reentry_frames

namespace P
open PaymentControl
/-- The G42 consumer adapter constructs sourceRaw from the exact raw-phase
execution. Marker/payment execution remains a restricted paired control. -/
def boundary : Premises origin := SourceBridge.premises origin code Observed Step
  (fun _ _ _ _ _ h => h.1)
  (fun _ _ _ _ _ h => h.2.2.2.2.2)
  premises.observed
  (by
    intro key machine raw state out h
    rw [h.2.2.1, h.2.2.2.1]
    exact (raw_iff origin _ _).mpr source_raw)
  (by
    intro key machine raw state out h
    rw [h.2.2.2.1]
    exact .start _ _)

theorem inhabited : boundary.Step (identity origin) initial (.ok (.success [])) sourceFinal (.ok final 0) :=
  PaymentControl.inhabited

theorem consumer :
    Evm.run boundary.code.full initial = .ok final 0 ∧ origin.RawAt (.ok (.success [])) sourceFinal :=
  ⟨(Callbacks.returned boundary _ _ _ _ _ inhabited).2.1,
    (Callbacks.returned boundary _ _ _ _ _ inhabited).2.2.2⟩
end P
end Solidity.Backend.WorldCalls.SourceBridgeControls
