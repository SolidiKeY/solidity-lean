import Solidity.Evm.MemoryRecursiveDemandViews

/-! Allocation-word bounds for real recursive certificates. The finite head's
bound is computed by its existing source prefixBudget. Nonallocating tails and
actual source stopping facts remove later costs; no execution cap is imposed. -/
namespace Solidity.Evm.Memory.Recursive
variable {C : Contract}
/-- Only the finite head can allocate; its bound is the existing computed source budget. -/
theorem demand_cons_base_nonallocating_le {b Γ Δ Ξ F G K s P head tail}
    (hs : Loops.StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s head)
    (hp : ProgCert b (Γ:=Δ) (Δ:=Ξ) G K P tail) (σ : State C Γ) (budget : Nat)
    (none : hp.allocates=false) (computed : Loops.prefixBudget (LoopScopes.singleton hs) σ=some budget)
    {amount} (demand : Demand (.cons (.base (.base hs)) hp) σ amount) : amount≤budget := by
  rcases Composition.demand_cons_cases demand with inner | ⟨out,spent,rest,run,cost,later,total⟩
  · exact Loops.demand_le_prefixBudget (LoopScopes.singleton hs) computed ((stmtDemand_base inner).view)
  · have zero := later.nonallocating none
    have headBound := Loops.demand_le_prefixBudget (LoopScopes.singleton hs) computed
      (LoopScopes.base_success_demand hs (stmtCost_base cost))
    omega

/-- Successful costs obey the same computed bound, including their nonallocating tail. -/
theorem cost_cons_base_nonallocating_le {b Γ Δ Ξ F G K s P head tail}
    (hs : Loops.StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s head)
    (hp : ProgCert b (Γ:=Δ) (Δ:=Ξ) G K P tail) (σ : State C Γ) (budget : Nat)
    (none : hp.allocates=false) (computed : Loops.prefixBudget (LoopScopes.singleton hs) σ=some budget)
    {out amount} (cost : Cost (.cons (.base (.base hs)) hp) σ out amount) : amount≤budget := by
  obtain ⟨mid,spent,rest,last,run,headCost,tailCost,total⟩ := cost_cons_cases cost
  have zero := tailCost.nonallocating none
  have headBound := Loops.demand_le_prefixBudget (LoopScopes.singleton hs) computed
    (LoopScopes.base_success_demand hs (stmtCost_base headCost))
  omega

/-- Only the initial body's demands and successful costs are reachable when
every successful body turn stops the next condition. -/
theorem stmtDemand_loop_one_turn_le {b Γ Δ F G body cond code} {c : Val C Γ .bool}
    (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G body code)
    (hc : ValFrag b F c cond) (stable : G.restrict Γ=F) (a : LoopAnn C Γ)
    (σ : State C Γ) (budget : Nat)
    (stops : ∀ (state : State C Γ) (out : Solidity.Out C state.H Δ),
      body.run state=.ok out → c.evalT (out.st.drop body.ext)=.ok false)
    (demandBound : ∀ amount,Demand hp σ amount → amount≤budget)
    (costBound : ∀ (out : Solidity.Out C σ.H Δ) amount,Cost hp σ out amount → amount≤budget)
    {amount} (demand : StmtDemand (.loop a hc hp stable) σ amount) : amount≤budget := by
  rcases stmtDemand_loop demand with ⟨out,before⟩ | ⟨out,spent,rest,before,tested,inner,rfl⟩
  · cases before with
    | start => exact Nat.zero_le _
    | next before tested run cost =>
      cases before with
      | start => simpa only [Nat.zero_add] using costBound _ _ cost
      | next older prior priorRun priorCost =>
        have no := stops _ _ priorRun
        rw [no] at tested
        cases tested
  · cases before with
    | start => simpa only [Nat.zero_add] using demandBound _ inner
    | next before prior run cost =>
      have no := stops _ _ run
      rw [no] at tested
      cases tested

/-- The nil continuation contributes no reached demand. -/
theorem demand_cons_nil_le {b Γ Δ F G s code}
    (hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code)
    (σ : State C Γ) (budget : Nat)
    (bound : ∀ amount,StmtDemand hs σ amount → amount≤budget)
    {amount} (demand : Demand (.cons hs (.nil G)) σ amount) : amount≤budget := by
  rcases Composition.demand_cons_cases demand with inner | ⟨out,spent,rest,run,cost,later,total⟩
  · exact bound _ inner
  · exact False.elim (Composition.demand_nil_false later)

end Solidity.Evm.Memory.Recursive
