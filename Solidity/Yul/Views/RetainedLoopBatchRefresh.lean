import Solidity.Yul.Views.RetainedLoopBatchCheckpoint

/-! A checked final write supplies the actual snapshot inventory and whole-map
reconstruction after any finite prefix of actual Source operations. Prefix
operations are executed, not represented by an assumed output simulation law.
Final preparation/separation and nonstatic permission remain explicit. Ordinary
halt preserves this reached state; no rollback or compiler adequacy is inferred. -/
namespace Solidity.Yul.Views.RetainedLoopBatchRefresh

theorem final_inventory {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (earlier : List (Source.Op E.layout E.lay E.lay))
    (last : Source.Op E.layout E.lay E.lay) (error : Source.Halt)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some last) :
    image.sourceInventory? (F:=F) ((RetainedLoopBatchCheckpoint.applyOpsThenHalt F (earlier++[last]) error).run state).2=some (image.snapshot raw) := by
  rw [RetainedLoopBatchCheckpoint.run_nonstatic F (earlier++[last]) state error static,
    Source.run_append]
  have direct := RetainedLoopRefresh.source_snapshot F image raw
    (state.1,{state.2 with ex := state.2.ex.run earlier}) last static checked prepared
  rw [actualApplyOp_run,static] at direct
  exact direct

theorem final_reencode {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (earlier : List (Source.Op E.layout E.lay E.lay))
    (last : Source.Op E.layout E.lay E.lay) (error : Source.Halt)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some last) :
    finiteEncode (image.snapshot raw) (((RetainedLoopBatchCheckpoint.applyOpsThenHalt F (earlier++[last]) error).run state).2.2.ex.world.accounts F.this).storage
      (packedMask (image.snapshot raw) raw)=some raw := by
  rw [RetainedLoopBatchCheckpoint.run_nonstatic F (earlier++[last]) state error static,
    Source.run_append]
  exact RetainedLoopWriteback.account_reencode image raw (state.2.ex.run earlier) last checked prepared

end Solidity.Yul.Views.RetainedLoopBatchRefresh
