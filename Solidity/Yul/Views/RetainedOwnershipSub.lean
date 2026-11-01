import Solidity.Yul.Views.RetainedOwnershipPlan

namespace Solidity.Yul.Views

theorem actualSubApply_run {E Γ Δ} (F : Source.Fr) (op : Source.Op E.layout E.lay E.lay)
    (s : Source.EMState E Γ) (callee : Source.Locals E.layout Δ) :
    (Source.EM.sub (Γ := Γ) callee (Source.applyOp F op)).run s =
      if F.static then (.error (.revert []),s)
      else (.ok ((),callee),(s.1,{s.2 with ex:=s.2.ex.apply op})) := by
  cases s with
  | mk locals state =>
    have evaluated : Source.applyOp F op (callee,state) =
        if F.static then (.error (.revert []),(callee,state))
        else (.ok (),(callee,{state with ex:=state.ex.apply op})) := actualApplyOp_run F op (callee,state)
    unfold Source.EM.sub
    cases static : F.static
    · simp only [static,Bool.false_eq_true,if_false] at evaluated ⊢
      simp only [ExceptT.run,ExceptT.mk,evaluated]
    · simp only [static,if_true] at evaluated ⊢
      simp only [ExceptT.run,ExceptT.mk,evaluated]

/-- One ACTUAL sub-local source operation, and complement writes gated by that
same result. Suspended caller history is not inferred from callee locals. -/
def RetainedOwnershipPlan.subStep {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    {Δ : Source.RCtx} (callee : Source.Locals E.layout Δ) :=
  let source := (Source.EM.sub (Γ := Γ) callee (Source.applyOp F p.sourceOp)).run s
  (source,(match source.1 with | .error _ => r | .ok _ => residualRun r p.updates),history)

theorem RetainedOwnershipPlan.sub_nonstatic {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    {Δ : Source.RCtx} (callee : Source.Locals E.layout Δ) (static : F.static=false) :
    p.subStep callee = ((.ok ((),callee),(s.1,{s.2 with ex:=s.2.ex.apply p.sourceOp})),residualRun r p.updates,history) := by
  unfold subStep
  rw [actualSubApply_run,static]
  rfl

theorem RetainedOwnershipPlan.sub_static {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    {Δ : Source.RCtx} (callee : Source.Locals E.layout Δ) (static : F.static=true) :
    p.subStep callee = ((.error (.revert []),s),r,history) := by
  unfold subStep
  rw [actualSubApply_run,static]
  rfl

theorem RetainedOwnershipPlan.sub_same_store {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    {Δ : Source.RCtx} (callee : Source.Locals E.layout Δ) :
    (p.subStep callee).1.2=p.step.1.2 ∧ (p.subStep callee).2=(p.step.2,history) := by
  cases static : F.static
  · rw [p.sub_nonstatic callee static,p.nonstatic static]
    exact ⟨rfl,rfl⟩
  · rw [p.sub_static callee static,p.static static]
    exact ⟨rfl,rfl⟩

/-- WHOLE map transport is derived for the same actual sub operation, not a
separately assumed pair of source/residual executions. -/
theorem RetainedOwnershipPlan.sub_reencode {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    {Δ : Source.RCtx} (callee : Source.Locals E.layout Δ) (static : F.static=false) :
    finiteEncode p.next ((p.subStep callee).1.2.2.ex.world.accounts F.this).storage
      (fun q => (p.subStep callee).2.1.cells (complementKey false F.this q))=some p.nextRaw := by
  rw [(p.sub_same_store callee).1,(p.sub_same_store callee).2]
  exact p.reencode static

theorem RetainedOwnershipPlan.sub_MemOK {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    {Δ : Source.RCtx} (callee : Source.Locals E.layout Δ) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (p.subStep callee).1.2 := by
  rw [(p.sub_same_store callee).1]
  exact p.MemOK H ok

end Solidity.Yul.Views
