import Solidity.Yul.Views.RetainedLoopRefresh

/-! Frame laws for actual checked captured-snapshot account writes. Canonical
preparation alone supplies the account/path/transient frame; static runs refuse
without change. Unrelated-path premises remain explicit, and no memory-write
correctness or general compiler/call adequacy is asserted. -/
namespace Solidity.Yul.Views.RetainedLoopFrame

theorem other_account {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation)
    (other : Roadmap.Address) (different : other≠F.this) :
    ((Source.applyOp (E:=E) (Γ:=Γ) F operation).run state).2.2.ex.world.accounts other=state.2.ex.world.accounts other := by
  rw [actualApplyOp_run]
  cases mode : F.static
  · change (state.2.ex.apply operation).world.accounts other=state.2.ex.world.accounts other
    obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp prepared
    rw [←same]
    exact Source.World.set_other _ different _
  · rfl

theorem other_path {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation)
    (path : Source.SPath) (unselected : ∀ c∈image.snapshot raw, path≠c.path) :
    (((Source.applyOp (E:=E) (Γ:=Γ) F operation).run state).2.2.ex.world.accounts F.this).storage.cell path=
      (state.2.ex.world.accounts F.this).storage.cell path := by
  rw [actualApplyOp_run]
  cases mode : F.static
  · change ((state.2.ex.apply operation).world.accounts F.this).storage.cell path=_
    exact finiteAccountWrite_other F.this (image.snapshot raw) raw state.2.ex operation prepared path unselected
  · rfl

theorem transient {E Γ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (state : Source.EMState E Γ) (operation : Source.Op E.layout E.lay E.lay)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation)
    : ((Source.applyOp (E:=E) (Γ:=Γ) F operation).run state).2.2.ex.transient=state.2.ex.transient := by
  rw [actualApplyOp_run]
  cases mode : F.static
  · obtain ⟨_,_,_,same,_⟩ := finiteAccountWrite_actual F.this (image.snapshot raw) raw state.2.ex operation prepared
    exact same
  · rfl

/-- Actual applyOp changes only ex; all locals/heap/event/log/function-local
administration is preserved, including a refused static run. -/
theorem administration {E Γ} (F : Source.Fr) (operation : Source.Op E.layout E.lay E.lay)
    (state : Source.EMState E Γ) :
    let reached := (Source.applyOp (E:=E) (Γ:=Γ) F operation).run state
    (reached.2.1,reached.2.2.heap,reached.2.2.events,reached.2.2.logs,reached.2.2.fnLocals)=
      (state.1,state.2.heap,state.2.events,state.2.logs,state.2.fnLocals) := by
  dsimp only
  rw [actualApplyOp_run]
  cases F.static <;> rfl

end Solidity.Yul.Views.RetainedLoopFrame
