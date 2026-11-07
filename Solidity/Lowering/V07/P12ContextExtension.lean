import Solidity.Lowering.V07.P12NextInterface

/-! Native context extension for an existing P12 condition producer. The
source expression/context and independent relations are unchanged. A typed
background supplies only initial local values, never an execution premise.
No admission, Source context extension, timeout or physical-copy adequacy is
claimed. Arbitrary thinnings and actual heap-growth weakening are reused. -/
namespace Solidity.Lowering.V07.P12ContextExtension
open P12NextInterface
variable {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ Δ : Ctx}

theorem aligned_lift (m : ContextMap srcΓ Γ) (values : ValueRelation E C) (worlds : WorldRelation E C)
    (s : Source.EMState E srcΓ) (t : State C Γ) (h : Thin Γ Δ) (d : TEnv C t.H Δ)
    (old : Aligned m values worlds s t) : Aligned (m.wk h) values worlds s (t.lift h d) := by
  exact ⟨old.1,ContextMap.related_wk m t (values s.2 t.glob) s.1 old.2 h d⟩

theorem aligned_thin (m : ContextMap srcΓ Γ) (values : ValueRelation E C) (worlds : WorldRelation E C)
    (s : Source.EMState E srcΓ) (t : State C Δ) (h : Thin Γ Δ)
    (old : Aligned (m.wk h) values worlds s t) : Aligned m values worlds s (t.thin h) := by
  refine ⟨old.1,?_⟩
  intro τ i
  have get := State.get_lift h (t.thin h) t.env (m.slot i).2
  have get' : TEnv.get ((m.slot i).2.wk h) t.env = TEnv.get (m.slot i).2 (t.thin h).env := by
    simpa only [State.lift,State.thin,State.withEnv,TEnv.put_thin] using get
  change values s.2 t.glob τ (m.slot i).1 (s.1.get i) (TEnv.get (m.slot i).2 (t.thin h).env)
  rw [← get']
  exact old.2 i

theorem operand_thin (e : DeferredSource.Operand C Γ (.prim .bool)) (h : Thin Γ Δ) (t : State C Δ) :
    (e.wk h).run t = liftedT₂ h t.env (e.run (t.thin h)) := by
  have commute := DeferredSource.Operand.run_wk e h (t.thin h) t.env
  let runEnv (d : TEnv C t.H Δ) : TRes (Out C t.H Δ × SVal (.prim .bool)) :=
    (e.wk h).run {t with env := d}
  have eta := congrArg runEnv (TEnv.put_thin h t.env)
  exact eta.symm.trans commute

theorem out_lift_glob (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ) (out : Out C H Γ) :
    (out.lift h d).st.glob = out.st.glob := by
  rfl

theorem out_lift_frame (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ) (out : Out C H Γ) :
    TEnv.off h (out.lift h d).st.env = offWk out.ext (TEnv.off h d) := by
  simp only [Out.lift,State.lift,State.withEnv,TEnv.off_put,TEnv.off_wk]

/-- Weaken the *whole contract*, not merely its already successful run. Every
aligned extended target is projected, executed, and lifted back. Background
locals are transported with the actual outcome heap extension by Out.lift. -/
def weaken (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C) (expr : Source.RExpr E srcΓ .bool)
    (input : Condition G F m values worlds expr) (h : Thin Γ Δ)
    (background : ∀ H : HTy, TEnv C H Δ) : Condition G F (m.wk h) values worlds expr where
  operand := input.operand.wk h
  initial_nonempty := by
    obtain ⟨s,t,old⟩ := input.initial_nonempty
    exact ⟨s,t.lift h (background t.H),aligned_lift m values worlds s t h (background t.H) old⟩
  success := by
    intro fuel s after t choice old run
    obtain ⟨out,native,post⟩ := input.success fuel s after (t.thin h) choice
      (aligned_thin m values worlds s t h old) run
    refine ⟨out.lift h t.env,?_,aligned_lift m values worlds after out.st h (TEnv.wk out.ext Δ t.env) post⟩
    rw [operand_thin,native]
    rfl
  revert := by
    intro fuel s after t data old run
    have native := input.revert fuel s after (t.thin h) data
      (aligned_thin m values worlds s t h old) run
    rw [operand_thin,native]
    rfl

/-- info: 'Solidity.Lowering.V07.P12ContextExtension.aligned_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtension.aligned_lift

/-- info: 'Solidity.Lowering.V07.P12ContextExtension.aligned_thin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtension.aligned_thin

/-- info: 'Solidity.Lowering.V07.P12ContextExtension.operand_thin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtension.operand_thin

/-- info: 'Solidity.Lowering.V07.P12ContextExtension.out_lift_glob' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtension.out_lift_glob

/-- info: 'Solidity.Lowering.V07.P12ContextExtension.out_lift_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtension.out_lift_frame

/-- info: 'Solidity.Lowering.V07.P12ContextExtension.weaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12ContextExtension.weaken

end Solidity.Lowering.V07.P12ContextExtension
