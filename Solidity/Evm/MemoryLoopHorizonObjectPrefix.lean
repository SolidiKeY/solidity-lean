import Solidity.Evm.MemoryObjectConstructionCompile
import Solidity.Evm.MemoryLoopFiniteHorizon

/-! Reached prefixes and finite allocation room for complete-object construction.
The cost is the construction compiler's actual cost, and allocation inputs use
the strong complete-object allocator. No legacy hpref/capacity is promoted;
these contracts alone do not assert target-loop transport or Source adequacy. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

/-- Actual successful source turns, with the complete-object construction cost. -/
inductive CountedLoopPrefix (c : Val C Γ .bool) (body : Prog C Γ Δ) (σ : State C Γ) :
    Solidity.Out C σ.H Γ → Nat → Nat → Prop where
  | start : CountedLoopPrefix c body σ ⟨σ, List.prefix_refl _⟩ 0 0
  | next {o : Solidity.Out C σ.H Γ} {cost turns : Nat}
      {next : Solidity.Out C o.st.H Δ}
      (hpref : CountedLoopPrefix c body σ o cost turns)
      (condition : c.evalT o.st = .ok true) (step : body.run o.st = .ok next) :
      CountedLoopPrefix c body σ ⟨next.st.drop body.ext, o.ext.trans next.ext⟩
        (cost + allocationCostProg body o.st) (turns + 1)

/-- Only reached true-condition turns below the horizon demand allocation room. -/
def FiniteLoopRoom (b frame : Nat) (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (σ : State C Γ) (base : Nat → Fin W) (machine : Machine) (horizon : Nat) : Prop :=
  ∀ (o : Solidity.Out C σ.H Γ) (cost turns : Nat), CountedLoopPrefix c body σ o cost turns →
    turns < horizon → c.evalT o.st = .ok true →
    Objects.AllocationInput b frame (cost + allocationCostProg body o.st) σ base machine

theorem CountedLoopPrefix.iterN_eq {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {o : Solidity.Out C σ.H Γ} {cost turns : Nat}
    (hpref : CountedLoopPrefix c body σ o cost turns) :
    TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) turns
      ⟨σ, List.prefix_refl _⟩ = .inl o := by
  induction hpref with
  | start => rfl
  | next hp hc hs ih =>
    rw [iterN_succ_of_pending ih]
    simp only [TLoop.step, hc, horizonBody, hs, Except.map]

theorem CountedLoopPrefix.cost_zero {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {o : Solidity.Out C σ.H Γ} {cost turns : Nat}
    (hpref : CountedLoopPrefix c body σ o cost turns)
    (nonallocating : hasAllocation body = false) : cost = 0 := by
  induction hpref with
  | start => rfl
  | next hp hc hs ih => rw [ih, allocationCostProg_zero body nonallocating]

theorem FiniteLoopRoom.prefix_input {b frame horizon : Nat} {c : Val C Γ .bool}
    {body : Prog C Γ Δ} {σ : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (room : FiniteLoopRoom b frame c body σ base machine horizon)
    {o : Solidity.Out C σ.H Γ} {cost turns : Nat}
    (hpref : CountedLoopPrefix c body σ o cost turns) (within : turns ≤ horizon) :
    Objects.AllocationInput b frame cost σ base machine := by
  cases hpref with
  | start => exact .inl rfl
  | next hp hc hs => exact room _ _ _ hp (by omega) hc

end Solidity.Evm.Memory.Construction
