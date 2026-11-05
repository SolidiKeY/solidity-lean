import Solidity.Yul.Views.RetainedLoopPayloadReadback
import Solidity.Yul.Views.RetainedLoopHeaderReadbackControls

/-! Bounds-checked Source indexing followed by packed payload readback at the
actual growth/shrink endpoints. The grown third cell and shrunk first cell read
77; a released index refuses before reading. These are fresh primitive runs,
not continuation through the earlier loop timeout or general capture adequacy. -/
namespace Solidity.Yul.Views.Controls

def rflprLoad (i : Nat) : Source.EM agEnv [] (Source.Val agEnv.layout (.int rcU16)) := do
  let loc ← Source.indexLoc packedStepFrame rhHeader.reference i
  Source.readLoc packedStepFrame loc

theorem rflpr_growth_view (G : Source.Glob agEnv) (flag : Bool) :
    scalarPathView (rhHeader.element agFixed account 2).path (rhHeader.element agFixed account 2).codec
      (rhHeader.element agFixed account 2).slot ((rflswRun G flag).2.2.ex.world.accounts account).storage rhNextRaw := by
  apply RetainedLoopPayloadReadback.source_payload packedStepFrame (rfliImage G flag) rhNextRaw
    (rflswState G flag) rhOp rfl (rflw_checked G flag) (rflw_prepared G flag) rhFirst.val (rfll_present G flag) rhHeaderEntry
  exact (rhHeader.elements_member agFixed account 3 _).mpr ⟨2,by decide,rfl⟩

theorem rflpr_shrink_view (G : Source.Glob agEnv) (flag : Bool) :
    scalarPathView (rhHeader.element agFixed account 0).path (rhHeader.element agFixed account 0).codec
      (rhHeader.element agFixed account 0).slot ((rflqRun G flag).2.2.ex.world.accounts account).storage rflqRaw := by
  apply RetainedLoopPayloadReadback.sequence_payload packedStepFrame (rfliImage G flag) rflqRaw
    (rflswState G flag) rhOp rflqOp .timeout rfl rflq_checked (rflq_prepared G flag) rhFirst.val (rfll_present G flag) rhHeaderEntry
  exact (rhHeader.elements_member agFixed account 1 _).mpr ⟨0,by decide,rfl⟩

theorem rflpr_growth_load (G : Source.Glob agEnv) (flag : Bool) :
    (rflprLoad 2).run (rflswRun G flag).2=(.ok (Source.intWrap rcU16 77),(rflswRun G flag).2) := by
  have read := rhHeader.read_element packedStepFrame (rflswRun G flag).2 agFixed 2 rhNextRaw
    rfl (rflpr_growth_view G flag)
  change (Source.readLoc packedStepFrame (.stor ((agInner 0).go (.index 2)))).run (rflswRun G flag).2=
    (.ok (Source.intWrap rcU16 77),(rflswRun G flag).2) at read
  unfold rflprLoad
  rw [Source.Hoare.run_bind,rflh_grown_index]
  exact read

theorem rflpr_shrink_load (G : Source.Glob agEnv) (flag : Bool) :
    (rflprLoad 0).run (rflqRun G flag).2=(.ok (Source.intWrap rcU16 77),(rflqRun G flag).2) := by
  have read := rhHeader.read_element packedStepFrame (rflqRun G flag).2 agFixed 0 rflqRaw
    rfl (rflpr_shrink_view G flag)
  change (Source.readLoc packedStepFrame (.stor ((agInner 0).go (.index 0)))).run (rflqRun G flag).2=
    (.ok (Source.intWrap rcU16 77),(rflqRun G flag).2) at read
  unfold rflprLoad
  rw [Source.Hoare.run_bind,rflh_live_index]
  exact read

theorem rflpr_released_load (G : Source.Glob agEnv) (flag : Bool) :
    (rflprLoad 1).run (rflqRun G flag).2=(.error (.revert (Source.panicData .index)),(rflqRun G flag).2) := by
  unfold rflprLoad
  rw [Source.Hoare.run_bind,rflh_released_index]

end Solidity.Yul.Views.Controls
