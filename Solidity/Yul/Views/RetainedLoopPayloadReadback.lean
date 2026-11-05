import Solidity.Yul.Views.RetainedLoopHeaderReadback

/-! Codec views for live payload registrations at actual checked Source write
endpoints. Live membership is checked against the newly read header length;
coverage and readback derive the output view, which is not a premise. No view
is granted to released indices, nor is global capture/physical adequacy claimed. -/
namespace Solidity.Yul.Views.RetainedLoopPayloadReadback

theorem source_payload {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation)
    (element : RetainedElementPack layout fixed) (present : element ∈ image.elements)
    (entry : {entry // entry ∈ child.headers
      (layout.path.go (.index element.1)) (layout.childCursor fixed element.1)})
    (c : ScalarPath E.layout (E.lay F.this))
    (live : c ∈ (element.2.header entry).elements fixed F.this
      (raw ((element.2.header entry).registration F.this).slot)) :
    scalarPathView c.path c.codec c.slot (((Source.applyOp F operation).run state).2.2.ex.world.accounts F.this).storage raw := by
  obtain ⟨n,read,covered⟩ := RetainedLoopLiveCoverage.source_live F image raw state operation
    static checked prepared element present entry
  have header := RetainedLoopHeaderReadback.source_header F image raw state operation
    static checked prepared element present entry
  have exactLength : aggregateSourceLengths F ((Source.applyOp F operation).run state).2
      ((element.2.header entry).registration F.this)=some (raw ((element.2.header entry).registration F.this).slot) := by
    unfold aggregateSourceLengths
    rw [PathPrimitiveHeader.registration_path,header]
    dsimp only [Except.toOption,Bind.bind,Option.bind]
    rw [dif_pos (raw ((element.2.header entry).registration F.this).slot).isLt]
  have same := Option.some.inj (read.symm.trans exactLength)
  subst n
  exact RetainedLoopRefresh.source_view F image raw state operation static checked prepared c (covered c live)

theorem sequence_payload {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ)
    (first second : Source.Op E.layout E.lay E.lay) (error : Source.Halt)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some second)
    (element : RetainedElementPack layout fixed) (present : element ∈ image.elements)
    (entry : {entry // entry ∈ child.headers
      (layout.path.go (.index element.1)) (layout.childCursor fixed element.1)})
    (c : ScalarPath E.layout (E.lay F.this))
    (live : c ∈ (element.2.header entry).elements fixed F.this
      (raw ((element.2.header entry).registration F.this).slot)) :
    scalarPathView c.path c.codec c.slot (((RetainedLoopSequence.writeTwiceThenHalt F first second error).run state).2.2.ex.world.accounts F.this).storage raw := by
  rw [RetainedLoopSequence.run F first second state error static]
  have direct := source_payload F image raw (state.1,{state.2 with ex := state.2.ex.apply first})
    second static checked prepared element present entry c live
  rw [actualApplyOp_run,static] at direct
  exact direct

end Solidity.Yul.Views.RetainedLoopPayloadReadback
