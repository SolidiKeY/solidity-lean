import Solidity.Backend.InternalFlow.ScopedLoopFrame

/-! A completed actual loop supplies its finite successful prefix. The existing
body guard and finite-prefix frame law then frame its reached state. Neither
the published withinM predicate nor loop/target semantics is extended. -/
namespace Solidity.Backend.InternalFlow

/-- Successful actual loops retain the admitted body's heap/local frame.
The finite horizon is derived from execution, never assumed or bounded. -/
theorem scoped_loop_completed_frame {C : Contract} {Γ Δ : Ctx}
    (μ : Mutability) (body : Prog C Γ Δ) (within : Prog.withinM μ body = true)
    (ann : LoopAnn C Γ) (condition : Val C Γ .bool)
    (initial : State C Γ) (out : Out C initial.H Γ)
    (executed : (Stmt.loop ann condition body).run initial = .ok out) :
    TGFrameM μ initial out.st out.ext ∧
      TLocAgreeM out.ext 0 (Prog.writesAt 0 body) initial.env out.st.env := by
  rw [Stmt.run_loop] at executed
  change TLoop.run (scopedLoopBody body) (fun o => condition.evalT o.st)
    ⟨initial,List.prefix_refl _⟩ = .ok out at executed
  have finite : ∃ n, TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) n
      ⟨initial,List.prefix_refl _⟩ = .inr (.ok out) := by
    unfold TLoop.run at executed
    split at executed
    · rename_i existsDone
      obtain ⟨n,hn⟩ := Classical.choose_spec existsDone
      exact ⟨n,executed ▸ hn⟩
    · cases executed
  obtain ⟨n,hn⟩ := finite
  exact scoped_loop_prefix_frame μ body within condition initial n out (.inr hn)

end Solidity.Backend.InternalFlow
