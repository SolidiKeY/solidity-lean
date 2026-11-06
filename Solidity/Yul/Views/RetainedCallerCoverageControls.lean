import Solidity.Yul.Views.RetainedCallerCoverage
import Solidity.Yul.Views.RetainedLocalAliasImageControls

/-! A suspended caller's two dormant children survive an empty-local callee
halt. The actual computed packing and source inventory retain both children.
These states/hash inputs are kernel seeds, not compiler constructor evidence. -/
namespace Solidity.Yul.Views.Controls
open RetainedCallerCoverage

def rccHalt : Source.EM agEnv [] (Source.Val agEnv.layout agAliasTy) := Source.EM.halt .timeout
def rccRun := captureSubValueRun packedStepFrame [] raState.1 Source.Locals.nil rccHalt raState.2

theorem rcc_source : rccRun.1=(.error .timeout,raState) := rfl
theorem rcc_visits : capturedVisitIndices rhLayout [] rccRun.2 0=[1,0] := rfl

def rccImage : CapturedArrayImage rhLayout agFixed [] rccRun.2 0 :=
  ⟨raiElements,by
    change rhLayout.prepareElements? agFixed (capturedVisitIndices rhLayout [] rccRun.2 0)=some raiElements
    rw [rcc_visits]
    exact Option.get_mem rai_elements_ready⟩

theorem rcc_prepared : prepareCapturedArrayImage? rhLayout agFixed [] rccRun.2 0=some rccImage :=
  CapturedArrayImage.prepared _

/-- Actual checked elements, not just scope/list projection, cover the caller. -/
theorem rcc_caller_element : ∃ element ∈ rccImage.elements, element.1=1 :=
  caller_element packedStepFrame rhLayout agFixed [] [] raState.1 Source.Locals.nil rccHalt raState.2
    0 rccImage (agInner 1) (by decide) 1 rfl

theorem rcc_typed : agEnv.pathTy (agInner 1)=some agAliasTy ∧
    ∃ element ∈ rccImage.elements, element.1=1 :=
  typed_caller_element packedStepFrame rhLayout agFixed [] [] raState.1 Source.Locals.nil rccHalt raState.2
    0 rccImage _ ra_initial_safe.1.2 .here (by rfl) (agInner 1) rfl 1 rfl

theorem rcc_snapshot : rccImage.snapshot rhRaw0=raiPaths .legacy := rfl

theorem rcc_view : finiteView (rccImage.snapshot rhRaw0) (rccRun.1.2.2.ex.world.accounts account).storage rhRaw0 := by
  rw [rcc_snapshot]
  exact rai_view .legacy

theorem rcc_inventory : rccImage.sourceInventory? (F:=packedStepFrame) rccRun.1.2=some (rccImage.snapshot rhRaw0) := by
  apply CapturedArrayImage.source_view (F:=packedStepFrame) rccImage rccRun.1.2 rhRaw0
  intro c member
  exact rcc_view c (RetainedLocalAliasImage.registration_mem_snapshot rccImage rhRaw0 c member)

theorem rcc_unchanged : capturedSnapshotWriteback rccImage rhRaw0
    (rccRun.1.2.2.ex.world.accounts account).storage=
      some ((rccRun.1.2.2.ex.world.accounts account).storage,packedMask (rccImage.snapshot rhRaw0) rhRaw0) := by
  apply capturedSnapshot_unchanged rccImage rhRaw0 _ _ rcc_view
  rw [rcc_snapshot]
  exact rai_separated .legacy

theorem rcc_reencode : finiteEncode (rccImage.snapshot rhRaw0)
    (rccRun.1.2.2.ex.world.accounts account).storage (packedMask (rccImage.snapshot rhRaw0) rhRaw0)=some rhRaw0 := by
  rw [rcc_snapshot]
  exact rai_reencode .legacy

/-- Capturing only the callee locals loses both retained child packs. -/
theorem rcc_missing_caller : capturedVisitIndices rhLayout [] [entryLocalScope packedStepFrame Source.Locals.nil] 0≠
    capturedVisitIndices rhLayout [] rccRun.2 0 := by
  rw [rcc_visits]
  decide
end Solidity.Yul.Views.Controls
