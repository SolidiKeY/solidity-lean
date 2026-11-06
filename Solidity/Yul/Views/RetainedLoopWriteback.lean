import Solidity.Yul.Views.RetainedLoopImage
import Solidity.Yul.Views.FiniteWorld

/-! Checked changed snapshots agree with an actual validated account operation
on current Source storage. Image computation, separation and operation preparation
remain explicit; this does not authorize static execution or supply EVM adequacy. -/
namespace Solidity.Yul.Views.RetainedLoopWriteback

theorem account_connection {E τ b child active a} {layout : @RetainedArrayLayout E τ b child active a}
    {fixed history scopes length} (image : CapturedArrayImage layout fixed history scopes length)
    (raw : SlotView) (state : Source.ExecState E.layout E.lay E.lay)
    (operation : Source.Op E.layout E.lay E.lay)
    (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? a (image.snapshot raw) raw=some operation) :
    capturedSnapshotWriteback image raw (state.world.accounts a).storage=
      some (((state.apply operation).world.accounts a).storage,packedMask (image.snapshot raw) raw) := by
  obtain ⟨out,decoded,actual,_,_⟩ := finiteAccountWrite_actual a (image.snapshot raw) raw state operation prepared
  unfold capturedSnapshotWriteback
  rw [checked]
  unfold packedStoreWriteback
  rw [decoded,Option.map_some,actual]
  rfl

/-- The same actual prepared Source operation reconstructs the whole changed
raw map from the updated Source store and the same snapshot's complement. -/
theorem account_reencode {E τ b child active a} {layout : @RetainedArrayLayout E τ b child active a}
    {fixed history scopes length} (image : CapturedArrayImage layout fixed history scopes length)
    (raw : SlotView) (state : Source.ExecState E.layout E.lay E.lay)
    (operation : Source.Op E.layout E.lay E.lay)
    (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? a (image.snapshot raw) raw=some operation) :
    finiteEncode (image.snapshot raw) ((state.apply operation).world.accounts a).storage
      (packedMask (image.snapshot raw) raw)=some raw := by
  exact capturedSnapshot_reencode image raw _ _ _ (account_connection image raw state operation checked prepared)

end Solidity.Yul.Views.RetainedLoopWriteback
