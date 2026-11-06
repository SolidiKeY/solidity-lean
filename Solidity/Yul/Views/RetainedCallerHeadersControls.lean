import Solidity.Yul.Views.RetainedCallerHeaders
import Solidity.Yul.Views.RetainedCallerCoverageControls

/-! Declaration-traced dormant child header in the actual halted-callee source
inventory. Physical coordinates and Source length agree for this kernel seed. -/
namespace Solidity.Yul.Views.Controls
open RetainedCallerHeaders

def rchEntry : {entry // entry ∈ agChild.headers (rhLayout.path.go (.index 1)) (rhLayout.childCursor agFixed 1)} :=
  ⟨(agInner 1,.integer rcU16,102*32+2),by decide⟩

theorem rch_image_header : ∃ header : PathPrimitiveHeader agEnv (agInner 1) (.integer rcU16) (102*32+2),
    header.registration account ∈ rccImage.registrations :=
  caller_header packedStepFrame rhLayout agFixed [] [] raState.1 Source.Locals.nil rccHalt raState.2 0 rccImage
    (agInner 1) (by decide) 1 rfl rchEntry

theorem rch_source_header : ∃ header : PathPrimitiveHeader agEnv (agInner 1) (.integer rcU16) (102*32+2),
    header.registration account ∈ rccImage.snapshot rhRaw0 :=
  caller_source_header packedStepFrame rhLayout agFixed [] [] raState.1 Source.Locals.nil rccHalt raState.2 0 rccImage
    (agInner 1) (by decide) 1 rfl rchEntry rccRun.1.2 _ rcc_inventory

theorem rch_view : ∃ header : PathPrimitiveHeader agEnv (agInner 1) (.integer rcU16) (102*32+2),
    scalarPathView (header.registration account).path (header.registration account).codec
      (header.registration account).slot (rccRun.1.2.2.ex.world.accounts account).storage rhRaw0 := by
  obtain ⟨header,member⟩ := rch_source_header
  exact ⟨header,rcc_view _ member⟩

theorem rch_coordinates (header : PathPrimitiveHeader agEnv (agInner 1) (.integer rcU16) (102*32+2)) :
    (header.registration account).path=agInner 1 ∧ (header.registration account).slot=103 ∧
    (header.registration account).field.offset=0 ∧ (header.registration account).field.width=32 :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem rch_typed_length : agEnv.cellTy (agInner 1)=.int .u256 ∧
    (Source.readLen packedStepFrame (agInner 1)).run rccRun.1.2=(.ok 1,rccRun.1.2) := ⟨rfl,rfl⟩

/-- A wrong sibling slot cannot satisfy the derived header coordinates. -/
theorem rch_not_sibling (header : PathPrimitiveHeader agEnv (agInner 1) (.integer rcU16) (102*32+2)) :
    (header.registration account).slot≠101 := by
  rw [(rch_coordinates header).2.1]
  decide
end Solidity.Yul.Views.Controls
