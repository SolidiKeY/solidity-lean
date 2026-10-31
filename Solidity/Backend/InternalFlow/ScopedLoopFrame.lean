import Solidity.Backend.InternalFlow.AllocationFrame
import Solidity.Backend.InternalFlow.PrefixLaws

/-! Finite-prefix consumers of the actual scoped body in TRun.loop.
No new loop evaluator, unbounded compiler simulation or rollback is defined. -/
namespace Solidity.Backend.InternalFlow

/-- Exactly TRun.loop's scoped body adapter: drop locals, compose heap growth. -/
def scopedLoopBody {C : Contract} {Γ Γ₁ : Ctx} {H : HTy}
    (body : Prog C Γ Γ₁) (previous : Out C H Γ) : TRes (Out C H Γ) :=
  (body.runR previous.st).map fun out => ⟨out.st.drop body.ext, previous.ext.trans out.ext⟩

/-- One successful actual scoped body transports the existing frame and local
agreement. The new body frame is derived from syntactic withinM admission. -/
theorem scoped_body_frame {C : Contract} {Γ Γ₁ : Ctx} (μ : Mutability)
    (body : Prog C Γ Γ₁) (within : Prog.withinM μ body = true)
    (initial : State C Γ) (previous next : Out C initial.H Γ)
    (frame : TGFrameM μ initial previous.st previous.ext)
    (locals : TLocAgreeM previous.ext 0 (Prog.writesAt 0 body) initial.env previous.st.env)
    (execution : scopedLoopBody body previous = .ok next) :
    TGFrameM μ initial next.st next.ext ∧
      TLocAgreeM next.ext 0 (Prog.writesAt 0 body) initial.env next.st.env := by
  unfold scopedLoopBody at execution
  obtain ⟨out, executed, rfl⟩ := tmap_ok_inv execution
  obtain ⟨bodyFrame, bodyLocals⟩ := Prog.run_frameM body within 0 executed
  exact ⟨(frame.trans bodyFrame _).withEnv _, locals.trans bodyLocals⟩

/-- Actual running or successfully completed finite horizons retain every old
heap object and untouched caller local. Failures carry no successful state. -/
theorem scoped_loop_prefix_frame {C : Contract} {Γ Γ₁ : Ctx} (μ : Mutability)
    (body : Prog C Γ Γ₁) (within : Prog.withinM μ body = true)
    (condition : Val C Γ .bool) (initial : State C Γ) (n : Nat)
    (out : Out C initial.H Γ)
    (hprefix : TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) n
      ⟨initial, List.prefix_refl _⟩ = .inl out ∨
      TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) n
      ⟨initial, List.prefix_refl _⟩ = .inr (.ok out)) :
    TGFrameM μ initial out.st out.ext ∧
      TLocAgreeM out.ext 0 (Prog.writesAt 0 body) initial.env out.st.env := by
  let invariant := fun o : Out C initial.H Γ => TGFrameM μ initial o.st o.ext ∧
    TLocAgreeM o.ext 0 (Prog.writesAt 0 body) initial.env o.st.env
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
        simp only [TLoop.iterN, TLoop.step, hc] at hp
        rcases hp with hp | hp <;> cases hp
      | ok flag =>
        cases flag with
        | false =>
          simp only [TLoop.iterN, TLoop.step, hc] at hp
          rcases hp with hp | hp
          · cases hp
          · cases hp; exact hs
        | true =>
          cases hb : scopedLoopBody body start with
          | error halt =>
            simp only [TLoop.iterN, TLoop.step, hc, hb] at hp
            rcases hp with hp | hp <;> cases hp
          | ok next =>
            simp only [TLoop.iterN, TLoop.step, hc, hb] at hp
            exact ih next finish (scoped_body_frame μ body within initial start next hs.1 hs.2 hb) hp
  apply key n ⟨initial, List.prefix_refl _⟩ out ?_ hprefix
  refine ⟨TGFrameM.ofFrame (TGFrame.refl initial) _, ?_⟩
  intro t i _ _
  exact (LTy.TDenote.wk_refl _ t (TEnv.get i initial.env)).symm

/-- info: 'Solidity.Backend.InternalFlow.scoped_body_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scoped_body_frame
/-- info: 'Solidity.Backend.InternalFlow.scoped_loop_prefix_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scoped_loop_prefix_frame

end Solidity.Backend.InternalFlow
