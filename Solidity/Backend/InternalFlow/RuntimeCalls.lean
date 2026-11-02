import Solidity.Backend.InternalFlow.FrameLaws

/-! Exact execution decomposition for ALL existing typed CallRet constructors.
This consumes TRun.call; it is neither a new evaluator nor target recursion. -/
namespace Solidity.Backend.InternalFlow.RuntimeCalls
variable {C : Contract} {Γ Δ ps rs Γf : Ctx}

/-- Canonical result construction of the existing call, with exact result-entry
and body extension and private-binder removal. No contents preservation claimed. -/
def returned (ret : CallRet Γ rs Δ) (scope : Ext (rs ++ ps) Γf)
    (caller : State C Γ) (arguments : TEnv C caller.H ps)
    (out : Out C (ret.enterT (caller.withEnv arguments)).st.H Γf) : Out C caller.H Δ :=
  ⟨out.st.withEnv (ret.leaveT
      (TEnv.wk ((ret.enterT (caller.withEnv arguments)).ext.trans out.ext) Γ caller.env)
      (TEnv.take rs (TEnv.drop scope out.st.env))),
    (ret.enterT (caller.withEnv arguments)).ext.trans out.ext⟩

/-- Extract actual dependent argument/body executions from actual call success.
No success or frame-preservation equation is a premise of the witness. -/
theorem success_iff (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (scope : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf)
    (caller : State C Γ) (final : Out C caller.H Δ) :
    TRun.call args ret scope body caller = .ok final ↔
      ∃ arguments : TEnv C caller.H ps, args.evalT caller = .ok arguments ∧
        ∃ out : Out C (ret.enterT (caller.withEnv arguments)).st.H Γf,
          body (ret.enterT (caller.withEnv arguments)).st = .ok out ∧
          returned ret scope caller arguments out = final := by
  constructor
  · intro ran
    unfold TRun.call at ran
    cases ha : args.evalT caller with
    | error e => simp only [ha, error_bind] at ran; cases ran
    | ok arguments =>
      simp only [ha, ok_bind] at ran
      cases hb : body (ret.enterT (caller.withEnv arguments)).st with
      | error e => simp only [hb, error_bind] at ran; cases ran
      | ok out =>
        simp only [hb, ok_bind] at ran
        exact ⟨arguments,rfl,out,hb,Except.ok.inj ran⟩
  · rintro ⟨arguments,ha,out,hb,eq⟩
    rw [← eq]
    exact call_return args ret scope body caller arguments ha out hb

/-- Failure class is exact, and is caused by argument evaluation OR the actual
entered body. This produces no failed State, rollback or execution trace. -/
theorem failure_iff (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (scope : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf)
    (caller : State C Γ) (halt : THalt) :
    TRun.call args ret scope body caller = .error halt ↔
      args.evalT caller = .error halt ∨
        ∃ arguments : TEnv C caller.H ps, args.evalT caller = .ok arguments ∧
          body (ret.enterT (caller.withEnv arguments)).st = .error halt := by
  unfold TRun.call
  cases ha : args.evalT caller with
  | error e =>
    simp only [error_bind]
    constructor
    · intro h
      cases Except.error.inj h
      exact .inl rfl
    · rintro (h | ⟨a,h,_⟩)
      · cases Except.error.inj h
        rfl
      · cases h
  | ok arguments =>
    simp only [ok_bind]
    cases hb : body (ret.enterT (caller.withEnv arguments)).st with
    | error e =>
      simp only [error_bind]
      constructor
      · intro h
        cases Except.error.inj h
        exact .inr ⟨arguments,rfl,hb⟩
      · rintro (h | ⟨a,h,failed⟩)
        · cases h
        · cases Except.ok.inj h
          cases Except.error.inj (hb.symm.trans failed)
          rfl
    | ok out =>
      simp only [ok_bind]
      constructor
      · intro h
        cases h
      · rintro (h | ⟨a,h,failed⟩)
        · cases h
        · cases Except.ok.inj h
          rw [hb] at failed
          cases failed
end Solidity.Backend.InternalFlow.RuntimeCalls
