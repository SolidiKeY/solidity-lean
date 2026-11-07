import Solidity.Yul.Views.RetainedLoopLiveCoverage

/-! Actual header reads at checked Source write endpoints for loop-captured
children. Layout provenance and finite-write preparation supply readback; no
caller-supplied read equality or arbitrary reference-formation law is needed.
The second operation is prepared against the final snapshot; ordinary halt
preserves its reached state and does not imply rollback. -/
namespace Solidity.Yul.Views.RetainedLoopHeaderReadback

theorem source_header {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation)
    (element : RetainedElementPack layout fixed) (present : element ∈ image.elements)
    (entry : {entry // entry ∈ child.headers
      (layout.path.go (.index element.1)) (layout.childCursor fixed element.1)}) :
    (Source.readLen F entry.val.1).run ((Source.applyOp F operation).run state).2=
      (.ok (raw ((element.2.header entry).registration F.this).slot).val,((Source.applyOp F operation).run state).2) := by
  have hm := element.2.header_member entry
  have bank : E.transientRoot entry.val.1=false := by
    have rootBank : E.transientRoot (layout.path.go (.index element.1))=false := layout.bank
    have hb := element.2.bank rootBank _ hm
    rw [PathPrimitiveHeader.registration_path] at hb
    exact hb
  have root := RetainedCallerHeaders.element_registration image element present _ hm
  have member := RetainedLocalAliasImage.registration_mem_snapshot image raw _ root
  exact (element.2.header entry).readLen_view F _ raw bank
    (RetainedLoopRefresh.source_view F image raw state operation static checked prepared _ member)

theorem sequence_header {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ)
    (first second : Source.Op E.layout E.lay E.lay) (error : Source.Halt)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some second)
    (element : RetainedElementPack layout fixed) (present : element ∈ image.elements)
    (entry : {entry // entry ∈ child.headers
      (layout.path.go (.index element.1)) (layout.childCursor fixed element.1)}) :
    (Source.readLen F entry.val.1).run ((RetainedLoopSequence.writeTwiceThenHalt F first second error).run state).2=
      (.ok (raw ((element.2.header entry).registration F.this).slot).val,((RetainedLoopSequence.writeTwiceThenHalt F first second error).run state).2) := by
  rw [RetainedLoopSequence.run F first second state error static]
  have direct := source_header F image raw (state.1,{state.2 with ex := state.2.ex.apply first})
    second static checked prepared element present entry
  rw [actualApplyOp_run,static] at direct
  exact direct

end Solidity.Yul.Views.RetainedLoopHeaderReadback
