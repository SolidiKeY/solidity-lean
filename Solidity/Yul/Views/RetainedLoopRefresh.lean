import Solidity.Yul.Views.RetainedLoopSourceSub
import Solidity.Yul.Views.RetainedLocalAliasImage

/-! Actual changed-write results supply refreshed captured source inventories.
View and inventory laws are derived from operation preparation, not added as
producer fields. Pure unchanged writeback is separate from executing a new op. -/
namespace Solidity.Yul.Views.RetainedLoopRefresh

theorem source_view {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation) :
    finiteView (image.snapshot raw) (((Source.applyOp F operation).run state).2.2.ex.world.accounts F.this).storage raw := by
  rw [actualApplyOp_run,static]
  exact finiteAccountWrite_view F.this (image.snapshot raw) raw state.2.ex operation
    ((packedSeparationCheck_iff _).mp checked) prepared

theorem source_snapshot {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation) :
    image.sourceInventory? (F:=F) ((Source.applyOp F operation).run state).2=some (image.snapshot raw) := by
  apply CapturedArrayImage.source_view (F:=F) image ((Source.applyOp F operation).run state).2 raw
  intro c member
  exact source_view F image raw state operation static checked prepared c
    (RetainedLocalAliasImage.registration_mem_snapshot image raw c member)

theorem source_unchanged {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation) :
    capturedSnapshotWriteback image raw (((Source.applyOp F operation).run state).2.2.ex.world.accounts F.this).storage=
      some ((((Source.applyOp F operation).run state).2.2.ex.world.accounts F.this).storage,packedMask (image.snapshot raw) raw) := by
  exact capturedSnapshot_unchanged image raw _ checked (source_view F image raw state operation static checked prepared)

theorem halt_snapshot {E Γ Δ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ) (state : Source.St E)
    (operation : Source.Op E.layout E.lay E.lay) (error : Source.Halt)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation) :
    image.sourceInventory? (F:=F)
      ((RetainedLoopSourceSub.writeThenHalt (E:=E) (Γ:=Γ) (Δ:=Δ) F operation callee error).run (caller,state)).2=
        some (image.snapshot raw) := by
  rw [RetainedLoopSourceSub.halt_run F operation caller callee state error static]
  have direct := source_snapshot F image raw (caller,state) operation static checked prepared
  rw [actualApplyOp_run,static] at direct
  exact direct

end Solidity.Yul.Views.RetainedLoopRefresh
