import Solidity.Yul.Views.RetainedLoopWriteback
import Solidity.Yul.Views.ComputedSnapshotSource

/-! The actual Source.applyOp boundary for a validated captured-snapshot write.
Nonstatic authorization is explicit. The existing Source rule supplies static
refusal and full state administration; no syntax or semantics is changed here. -/
namespace Solidity.Yul.Views.RetainedLoopSourceWrite

theorem source_connection {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation) :
    capturedSnapshotWriteback image raw (state.2.ex.world.accounts F.this).storage=
      some ((((Source.applyOp F operation).run state).2.2.ex.world.accounts F.this).storage,
        packedMask (image.snapshot raw) raw) := by
  rw [actualApplyOp_run,static]
  exact RetainedLoopWriteback.account_connection image raw state.2.ex operation checked prepared

theorem source_reencode {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation) :
    finiteEncode (image.snapshot raw)
      (((Source.applyOp F operation).run state).2.2.ex.world.accounts F.this).storage
      (packedMask (image.snapshot raw) raw)=some raw := by
  exact capturedSnapshot_reencode image raw _ _ _ (source_connection F image raw state operation static checked prepared)

end Solidity.Yul.Views.RetainedLoopSourceWrite
