import Solidity.Yul.Views.RetainedLoopRefresh

/-! Explicit journal rollback of one actual Source.applyOp run. The checkpoint
is recorded before that run and keeps the real frame input. This adapter does
not make an interpreter halt invoke rollback or supply external-call adequacy. -/
namespace Solidity.Yul.Views.RetainedLoopCheckpoint

def rollbackApply {E Γ} (F : Source.Fr) (operation : Source.Op E.layout E.lay E.lay)
    (state : Source.EMState E Γ) : Except Source.Halt Unit × Source.EMState E Γ :=
  let reached := (Source.applyOp (E:=E) (Γ:=Γ) F operation).run state
  let checkpoint := state.2.ex.enter F.this F.sender F.value F.cd F.static
  (reached.1,(reached.2.1,{reached.2.2 with ex := checkpoint.rollback reached.2.2.ex}))

/-- Explicit rollback restores the whole state while retaining the actual
success or static-refusal result of the primitive run. -/
theorem rollback_result {E Γ} (F : Source.Fr) (operation : Source.Op E.layout E.lay E.lay)
    (state : Source.EMState E Γ) :
    rollbackApply F operation state=
      if F.static then (.error (.revert []),state) else (.ok (),state) := by
  unfold rollbackApply
  rw [actualApplyOp_run]
  cases mode : F.static
  · simp only [Bool.false_eq_true,if_false]
    have undo := Source.rollback_run state.2.ex [operation] F.this F.sender F.value F.cd false
    change (state.2.ex.enter F.this F.sender F.value F.cd false).rollback (state.2.ex.apply operation)=state.2.ex at undo
    rw [undo]
  · simp only [if_true]
    have undo := Source.rollback_run state.2.ex [] F.this F.sender F.value F.cd true
    change (state.2.ex.enter F.this F.sender F.value F.cd true).rollback state.2.ex=state.2.ex at undo
    rw [undo]

end Solidity.Yul.Views.RetainedLoopCheckpoint
