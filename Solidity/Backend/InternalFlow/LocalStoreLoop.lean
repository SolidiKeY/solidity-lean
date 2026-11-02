import Solidity.Backend.InternalFlow.LocalStoreFlow
import Solidity.Backend.InternalFlow.ScopedLoopFrame
/-! Local-only frames for the actual scoped loop body. The typed body plan,
not withinM for the entire body or a postulated loop invariant, discharges the
step. No heap-content preservation or storage-alias liveness follows. -/
namespace Solidity.Backend.InternalFlow.LocalStoreFlow
variable {C : Contract} {Γ Δ : Ctx} {t : LTy}

/-- One real iteration drops its private locals and composes the real heap extension. -/
theorem ProgPlan.scoped_step {body : Prog C Γ Δ} {i : Idx Γ t}
    (plan : ProgPlan t body i) (initial : State C Γ)
    (previous next : Out C initial.H Γ)
    (before : TEnv.get i previous.st.env =
      LTy.TDenote.wk previous.ext t (TEnv.get i initial.env))
    (ran : scopedLoopBody body previous = .ok next) :
    TEnv.get i next.st.env = LTy.TDenote.wk next.ext t (TEnv.get i initial.env) := by
  unfold scopedLoopBody at ran
  obtain ⟨out,executed,rfl⟩ := tmap_ok_inv ran
  change TEnv.get i (TEnv.drop body.ext out.st.env) = _
  rw [plan.sound executed,before,LTy.TDenote.wk_wk]

/-- Running and successfully completed finite horizons preserve the protected
binding even when actual heap contents and storage change. Error horizons
supply no successful state. -/
theorem ProgPlan.loop_prefix {body : Prog C Γ Δ} {i : Idx Γ t}
    (plan : ProgPlan t body i) (condition : Val C Γ .bool)
    (initial : State C Γ) (n : Nat) (out : Out C initial.H Γ)
    (ran : TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) n
      ⟨initial,List.prefix_refl _⟩ = .inl out ∨
      TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) n
      ⟨initial,List.prefix_refl _⟩ = .inr (.ok out)) :
    TEnv.get i out.st.env = LTy.TDenote.wk out.ext t (TEnv.get i initial.env) := by
  let invariant := fun o : Out C initial.H Γ =>
    TEnv.get i o.st.env = LTy.TDenote.wk o.ext t (TEnv.get i initial.env)
  have key : ∀ k (start finish : Out C initial.H Γ), invariant start →
      (TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) k start = .inl finish ∨
       TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) k start = .inr (.ok finish)) →
      invariant finish := by
    intro k
    induction k with
    | zero =>
      intro start finish hs hp
      rcases hp with hp | hp
      · cases hp; exact hs
      · cases hp
    | succ k ih =>
      intro start finish hs hp
      cases hc : condition.evalT start.st with
      | error halt =>
        simp only [TLoop.iterN,TLoop.step,hc] at hp
        rcases hp with hp | hp <;> cases hp
      | ok flag =>
        cases flag with
        | false =>
          simp only [TLoop.iterN,TLoop.step,hc] at hp
          rcases hp with hp | hp
          · cases hp
          · cases hp; exact hs
        | true =>
          cases hb : scopedLoopBody body start with
          | error halt =>
            simp only [TLoop.iterN,TLoop.step,hc,hb] at hp
            rcases hp with hp | hp <;> cases hp
          | ok next =>
            simp only [TLoop.iterN,TLoop.step,hc,hb] at hp
            exact ih next finish (plan.scoped_step initial start next hs hb) hp
  exact key n _ out (LTy.TDenote.wk_refl _ t (TEnv.get i initial.env)).symm ran

/-- Successful execution uses the published unbounded run induction. The
error/divergence cases remain errors, with no invented output State. -/
theorem ProgPlan.loop_success {body : Prog C Γ Δ} {i : Idx Γ t}
    (plan : ProgPlan t body i) (condition : Val C Γ .bool)
    (initial : State C Γ) (out : Out C initial.H Γ)
    (ran : TRun.loop condition body.ext body.runR initial = .ok out) :
    TEnv.get i out.st.env = LTy.TDenote.wk out.ext t (TEnv.get i initial.env) := by
  let invariant := fun o : Out C initial.H Γ =>
    TEnv.get i o.st.env = LTy.TDenote.wk o.ext t (TEnv.get i initial.env)
  let outcome := fun r : TRes (Out C initial.H Γ) =>
    match r with | .ok o => invariant o | .error _ => True
  have result : outcome (TLoop.run (scopedLoopBody body) (fun o => condition.evalT o.st)
      ⟨initial,List.prefix_refl _⟩) := by
    apply TLoop.run_induct (P := invariant)
    · exact (LTy.TDenote.wk_refl _ t (TEnv.get i initial.env)).symm
    · intro start hs
      cases hc : condition.evalT start.st with
      | error halt => simp only [TLoop.step,hc]; trivial
      | ok flag =>
        cases flag with
        | false => simp only [TLoop.step,hc]; exact hs
        | true =>
          cases hb : scopedLoopBody body start with
          | error halt => simp only [TLoop.step,hc,hb]; trivial
          | ok next => simp only [TLoop.step,hc,hb]; exact plan.scoped_step initial start next hs hb
    · trivial
  change TLoop.run (scopedLoopBody body) (fun o => condition.evalT o.st)
    ⟨initial,List.prefix_refl _⟩ = .ok out at ran
  rw [ran] at result
  exact result

theorem ProgPlan.loop_statement {body : Prog C Γ Δ} {i : Idx Γ t}
    (plan : ProgPlan t body i) (ann : LoopAnn C Γ) (condition : Val C Γ .bool)
    (initial : State C Γ) (out : Out C initial.H Γ)
    (ran : (Stmt.loop ann condition body).run initial = .ok out) :
    TEnv.get i out.st.env = LTy.TDenote.wk out.ext t (TEnv.get i initial.env) := by
  rw [Stmt.run_loop] at ran
  exact plan.loop_success condition initial out ran
end Solidity.Backend.InternalFlow.LocalStoreFlow
