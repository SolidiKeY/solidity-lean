import Solidity.Yul.Views.RetainedLoopHeaderReadback
import Solidity.Yul.Views.RetainedLoopLiveCoverageControls

/-! Actual header reads govern indexing on the same retained reference. Growth
admits index two, shrink retains index zero and rejects index one with the real
Source index panic. Persisting Source cells do not grant live index access.
These checks compose fresh primitive runs after the captured loop endpoint;
they do not bind through its timeout or establish general reference formation. -/
namespace Solidity.Yul.Views.Controls

theorem rflh_growth (G : Source.Glob agEnv) (flag : Bool) :
    (Source.readLen packedStepFrame (agInner 0)).run (rflswRun G flag).2=
      (.ok 3,(rflswRun G flag).2) := by
  exact RetainedLoopHeaderReadback.source_header packedStepFrame (rfliImage G flag) rhNextRaw
    (rflswState G flag) rhOp rfl (rflw_checked G flag) (rflw_prepared G flag)
    rhFirst.val (rfll_present G flag) rhHeaderEntry

theorem rflh_shrink (G : Source.Glob agEnv) (flag : Bool) :
    (Source.readLen packedStepFrame (agInner 0)).run (rflqRun G flag).2=
      (.ok 1,(rflqRun G flag).2) := by
  exact RetainedLoopHeaderReadback.sequence_header packedStepFrame (rfliImage G flag) rflqRaw
    (rflswState G flag) rhOp rflqOp .timeout rfl rflq_checked (rflq_prepared G flag)
    rhFirst.val (rfll_present G flag) rhHeaderEntry

theorem rflh_grown_index (G : Source.Glob agEnv) (flag : Bool) :
    (Source.indexLoc packedStepFrame rhHeader.reference 2).run (rflswRun G flag).2=
      (.ok (.stor ((agInner 0).go (.index 2))),(rflswRun G flag).2) := by
  exact rhHeader.indexLoc packedStepFrame (rflswRun G flag).2 3 (rflh_growth G flag) 2

theorem rflh_live_index (G : Source.Glob agEnv) (flag : Bool) :
    (Source.indexLoc packedStepFrame rhHeader.reference 0).run (rflqRun G flag).2=
      (.ok (.stor ((agInner 0).go (.index 0))),(rflqRun G flag).2) := by
  exact rhHeader.indexLoc packedStepFrame (rflqRun G flag).2 1 (rflh_shrink G flag) 0

theorem rflh_released_index (G : Source.Glob agEnv) (flag : Bool) :
    (Source.indexLoc packedStepFrame rhHeader.reference 1).run (rflqRun G flag).2=
      (.error (.revert (Source.panicData .index)),(rflqRun G flag).2) := by
  exact rhHeader.indexLoc packedStepFrame (rflqRun G flag).2 1 (rflh_shrink G flag) 1

end Solidity.Yul.Views.Controls
