import Solidity.Yul.Views.RetainedLoopFrame

/-! Two actual Source operations followed by ordinary interpreter halt. The
second write uses the reached first-write state; its preparation and separation
supply final reconstruction and refreshed source traversal. No rollback or
whole-program/compiler adequacy is inferred. -/
namespace Solidity.Yul.Views.RetainedLoopSequence

def writeTwiceThenHalt {E Γ} (F : Source.Fr) (first second : Source.Op E.layout E.lay E.lay)
    (error : Source.Halt) : Source.EM E Γ Unit := do
  Source.applyOp F first
  Source.applyOp F second
  Source.EM.halt error

theorem run {E Γ} (F : Source.Fr) (first second : Source.Op E.layout E.lay E.lay)
    (state : Source.EMState E Γ) (error : Source.Halt) (static : F.static=false) :
    (writeTwiceThenHalt F first second error).run state=
      (.error error,(state.1,{state.2 with ex := (state.2.ex.apply first).apply second})) := by
  simp only [writeTwiceThenHalt,Source.Hoare.run_bind,actualApplyOp_run,static,Bool.false_eq_true,if_false]
  rfl

theorem final_reencode {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (first second : Source.Op E.layout E.lay E.lay) (error : Source.Halt)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some second) :
    finiteEncode (image.snapshot raw)
      (((writeTwiceThenHalt F first second error).run state).2.2.ex.world.accounts F.this).storage
      (packedMask (image.snapshot raw) raw)=some raw := by
  rw [run F first second state error static]
  exact RetainedLoopWriteback.account_reencode image raw (state.2.ex.apply first) second checked prepared

theorem final_inventory {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (first second : Source.Op E.layout E.lay E.lay) (error : Source.Halt)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some second) :
    image.sourceInventory? (F:=F) ((writeTwiceThenHalt F first second error).run state).2=
      some (image.snapshot raw) := by
  rw [run F first second state error static]
  have direct := RetainedLoopRefresh.source_snapshot F image raw
    (state.1,{state.2 with ex := state.2.ex.apply first}) second static checked prepared
  rw [actualApplyOp_run,static] at direct
  exact direct

end Solidity.Yul.Views.RetainedLoopSequence
