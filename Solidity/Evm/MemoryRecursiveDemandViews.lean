import Solidity.Evm.MemoryRecursiveBranchRoom
import Solidity.Evm.MemoryLoopScopeBudget

/-! Typed elimination views of existing recursive costs and demands.
No source syntax, execution or compiler certificate is redefined. -/
namespace Solidity.Evm.Memory.Recursive
variable {C : Contract}
/-- A base demand is the same existing scoped demand. -/
theorem stmtDemand_base {b Γ Δ F G s code}
    {hs : LoopScopes.StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code}
    {σ : State C Γ} {amount} (demand : StmtDemand (.base hs) σ amount) :
    LoopScopes.StmtDemand hs σ amount := by
  cases demand with
  | base inner => exact inner

/-- A base cost retains its exact typed source output and scoped cost. -/
theorem stmtCost_base {b Γ Δ F G s code}
    {hs : LoopScopes.StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code}
    {σ : State C Γ} {out amount} (cost : StmtCost (.base hs) σ out amount) :
    LoopScopes.StmtCost hs σ out amount := by
  cases cost with
  | base inner => exact inner

/-- A loop demand is a completed prefix or an active body after a prefix. -/
theorem stmtDemand_loop {b Γ Δ F G c body cond code}
    {hc : ValFrag (C:=C) b (Γ:=Γ) F c cond}
    {hp : ProgCert b (Γ:=Γ) (Δ:=Δ) F G body code} {stable : G.restrict Γ=F}
    {a : LoopAnn C Γ} {σ : State C Γ} {amount}
    (demand : StmtDemand (.loop a hc hp stable) σ amount) :
    (∃ out,LoopPrefix hp c σ out amount) ∨
    ∃ out spent rest,LoopPrefix hp c σ out spent ∧ c.evalT out.st=.ok true ∧
      Demand hp out.st rest ∧ amount=spent+rest := by
  cases demand with
  | loopPrefix before => exact Or.inl ⟨_,before⟩
  | loopBody before condition inner => exact Or.inr ⟨_,_,_,before,condition,inner,rfl⟩

private def costShape {b Γ Δ F G P code}
    (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code)
    (σ : State C Γ) (amount : Nat) : Prop :=
  ProgCert.casesOn
    (motive_2:=fun {Γ _Δ} _F _G _P _code _hp=>State C Γ → Nat → Prop) hp
    (fun _ _ amount=>amount=0)
    (fun {_Γ Δ Ξ _F _G _K s _P _head _tail} hs hp σ amount=>
      ∃ (mid : Solidity.Out C σ.H Δ) (spent rest : Nat) (last : Solidity.Out C mid.st.H Ξ),
        s.run σ=.ok mid ∧ StmtCost hs σ mid spent ∧ Cost hp mid.st last rest ∧ amount=spent+rest)
    σ amount

private theorem cost_shape {b Γ Δ F G P code}
    {hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code}
    {σ : State C Γ} {out amount} (cost : Cost hp σ out amount) : costShape hp σ amount := by
  cases cost with
  | nil => rfl
  | cons run head tail => exact ⟨_,_,_,_,run,head,tail,rfl⟩

/-- Actual source head run and both costs, with their exact total. -/
theorem cost_cons_cases {b Γ Δ Ξ F G K s P head tail}
    {hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s head}
    {hp : ProgCert b (Γ:=Δ) (Δ:=Ξ) G K P tail} {σ : State C Γ} {out amount}
    (cost : Cost (.cons hs hp) σ out amount) :
    ∃ (mid : Solidity.Out C σ.H Δ) (spent rest : Nat) (last : Solidity.Out C mid.st.H Ξ),
      s.run σ=.ok mid ∧ StmtCost hs σ mid spent ∧ Cost hp mid.st last rest ∧ amount=spent+rest := by
  exact cost_shape cost

end Solidity.Evm.Memory.Recursive
