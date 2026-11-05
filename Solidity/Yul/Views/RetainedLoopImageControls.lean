import Solidity.Yul.Views.RetainedLoopImage
import Solidity.Yul.Views.RetainedForLoopPostControls
import Solidity.Yul.Views.RetainedStorageControls
import Solidity.Yul.Views.RetainedLocalAliasImage

/-! Reached loop-post captures select a dormant checked child at zero live
length and no formation history. This is finite image/source/writeback agreement
for kernel fixtures, not allocator provenance or general compiler adequacy. -/
namespace Solidity.Yul.Views.Controls

def rfliRun (G : Source.Glob agEnv) (flag : Bool) :=
  (rflpObserver G flag).observe [] agShrink.2.1 rsOuter

theorem rfli_visits (G : Source.Glob agEnv) (flag : Bool) :
    capturedVisitIndices rhLayout [] (rfliRun G flag).2 0=[0] := by
  cases flag <;> rfl

def rfliImage (G : Source.Glob agEnv) (flag : Bool) :
    CapturedArrayImage rhLayout agFixed [] (rfliRun G flag).2 0 where
  elements := rhImage.elements
  computed := by
    change rhLayout.prepareElements? agFixed (capturedVisitIndices rhLayout [] (rfliRun G flag).2 0)=some rhImage.elements
    rw [rfli_visits]
    exact rhImage.computed

theorem rfli_prepared (G : Source.Glob agEnv) (flag : Bool) :
    prepareCapturedArrayImage? rhLayout agFixed [] (rfliRun G flag).2 0=some (rfliImage G flag) :=
  CapturedArrayImage.prepared _

theorem rfli_element (G : Source.Glob agEnv) (flag : Bool) :
    ∃ element∈(rfliImage G flag).elements, element.1=0 :=
  RetainedLoopImage.scope_element rhLayout agFixed [] (rfliRun G flag).2 0 (rfliImage G flag)
    (runtimeScope packedStepFrame (.val rtAlias)) (rflp_post_head G flag) rfl
    (agInner 0) (by decide) 0 rfl

theorem rfli_snapshot (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).snapshot rhRaw0=rhOld := rfl

theorem rfli_view (G : Source.Glob agEnv) (flag : Bool) :
    finiteView ((rfliImage G flag).snapshot rhRaw0)
      ((rfliRun G flag).1.2.2.ex.world.accounts account).storage rhRaw0 := by
  have reached : (rfliRun G flag).1.2=rsOuter := congrArg Prod.snd (rflp_late_timeout G flag)
  rw [reached,rfli_snapshot]
  exact rh_view

theorem rfli_source_inventory (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rfliRun G flag).1.2=
      some ((rfliImage G flag).snapshot rhRaw0) := by
  apply CapturedArrayImage.source_view (F:=packedStepFrame) (rfliImage G flag) (rfliRun G flag).1.2 rhRaw0
  intro c member
  exact rfli_view G flag c (RetainedLocalAliasImage.registration_mem_snapshot (rfliImage G flag) rhRaw0 c member)

theorem rfli_unchanged (G : Source.Glob agEnv) (flag : Bool) :
    capturedSnapshotWriteback (rfliImage G flag) rhRaw0
      ((rfliRun G flag).1.2.2.ex.world.accounts account).storage=
        some (((rfliRun G flag).1.2.2.ex.world.accounts account).storage,
          packedMask ((rfliImage G flag).snapshot rhRaw0) rhRaw0) := by
  apply capturedSnapshot_unchanged (rfliImage G flag) rhRaw0 _
  · rw [rfli_snapshot]
    exact rh_separated
  · exact rfli_view G flag

theorem rfli_reencode (G : Source.Glob agEnv) (flag : Bool) :
    finiteEncode ((rfliImage G flag).snapshot rhRaw0)
      ((rfliRun G flag).1.2.2.ex.world.accounts account).storage
      (packedMask ((rfliImage G flag).snapshot rhRaw0) rhRaw0)=some rhRaw0 := by
  exact capturedSnapshot_reencode (rfliImage G flag) rhRaw0 _ _ _ (rfli_unchanged G flag)

/-- Omitting observations at zero length and empty history loses this child. -/
theorem rfli_missing_observation (G : Source.Glob agEnv) (flag : Bool) :
    capturedVisitIndices rhLayout [] [] 0≠capturedVisitIndices rhLayout [] (rfliRun G flag).2 0 := by
  rw [rfli_visits]
  decide

end Solidity.Yul.Views.Controls
