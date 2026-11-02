import Solidity.Backend.InternalFlow.RuntimeCalls
import Solidity.Calculus.RunFrameMem

/-! General typed successful-call frame consumer for the EXISTING withinM
profile. It does not admit arbitrary old-object writes or static world calls. -/
namespace Solidity.Backend.InternalFlow.RuntimeGuardedFrame
variable {C : Contract} {Γ Δ ps rs Γf : Ctx}

/-- The same actual successful call has its syntax-derived frame AND exact
argument/body/result decomposition, for every existing result constructor. -/
theorem success (μ : Mutability) (name : Name) (args : Args C Γ ps)
    (ret : CallRet Γ rs Δ) (body : Prog C (rs ++ ps) Γf)
    (reads : args.readsIn μ = true) (within : Prog.withinM μ body = true)
    (caller : State C Γ) (final : Out C caller.H Δ)
    (ran : TRun.call args ret body.ext body.runR caller = .ok final) :
    TGFrameM μ caller final.st final.ext ∧
    TLocAgreeM final.ext 0 ((Stmt.call name args ret body).writesAt 0) caller.env
      (TEnv.drop (Stmt.call name args ret body).ext final.st.env) ∧
    ∃ a : TEnv C caller.H ps, args.evalT caller = .ok a ∧
      ∃ out : Out C (ret.enterT (caller.withEnv a)).st.H Γf,
        body.runR (ret.enterT (caller.withEnv a)).st = .ok out ∧
        RuntimeCalls.returned ret body.ext caller a out = final := by
  have hw : (Stmt.call name args ret body).withinM μ = true := by
    simp only [Stmt.withinM,reads,within,Bool.true_and,Bool.or_true]
  have actual : (Stmt.call name args ret body).run caller = .ok final := ran
  obtain ⟨frame,locals⟩ := Stmt.run_frameM (Stmt.call name args ret body) hw 0 actual
  exact ⟨frame,locals,(RuntimeCalls.success_iff args ret body.ext body.runR caller final).mp ran⟩
end Solidity.Backend.InternalFlow.RuntimeGuardedFrame
