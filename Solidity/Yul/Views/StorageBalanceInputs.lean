import Solidity.Yul.Views.SourceBalanceInputs
import Solidity.Yul.Views.PackedResidualSource

namespace Solidity.Yul.Views

/-- Derived from the actual validator-produced account operation. The update
may alter storage and journal administration; code and balance are unchanged
at EVERY address, including the selected account. -/
theorem finiteAccountWrite_balance_fields {D L T}
    (a : Roadmap.Address) (cs : List (ScalarPath D (L a))) (raw : SlotView)
    (s : Source.ExecState D L T) (op : Source.Op D L T)
    (prepared : finiteAccountWrite? a cs raw = some op) (b : Roadmap.Address) :
    ((s.apply op).world.accounts b).code = (s.world.accounts b).code ∧
    ((s.apply op).world.accounts b).balance = (s.world.accounts b).balance := by
  obtain ⟨update, _, same⟩ := Option.map_eq_some_iff.mp prepared
  subst op
  by_cases eq : b=a
  · subst b
    simp only [Source.ExecState.apply,Source.World.set_get, and_self]
  · simp only [Source.ExecState.apply,Source.World.set_other _ eq, and_self]

/-- The persistent/transient choice comes from the SAME validated raw plan.
No free account operation is presumed to preserve monetary observations. -/
theorem packedPlan_balance_fields {D L T ps ts}
    (p : @PackedSlotPlan D L T ps ts) (s : Source.ExecState D L T) (b : Roadmap.Address) :
    ((s.apply p.sourceOp).world.accounts b).code = (s.world.accounts b).code ∧
    ((s.apply p.sourceOp).world.accounts b).balance = (s.world.accounts b).balance := by
  have prepared := p.prepared
  unfold packedRequestOp? at prepared
  cases bank : p.request.transient
  · rw [bank] at prepared
    exact finiteAccountWrite_balance_fields _ _ _ s _ prepared b
  · rw [bank] at prepared
    obtain ⟨update, _, same⟩ := Option.map_eq_some_iff.mp prepared
    rw [←same]
    exact ⟨rfl,rfl⟩

/-- Exact constructed balance snapshot is invariant through the actual
static-checked source/residual step, on BOTH success and empty-revert failure.
The external branch retains the SAME original event history and Fixed.ledger. -/
theorem packedSourceStep_observed_balance {E Γ ps ts}
    (G : Source.Glob E) (F : Source.Fr) (p : @PackedSlotPlan E.layout E.lay E.lay ps ts)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) (b : Roadmap.Address) :
    sourceObservedBalance G (packedSourceStep F p s r).1.2 b = sourceObservedBalance G s b := by
  cases static : F.static
  · rw [packedSourceStep_nonstatic F p s r static]
    obtain ⟨code,balance⟩ := packedPlan_balance_fields p s.2.ex b
    unfold sourceObservedBalance
    change (match ((s.2.ex.apply p.sourceOp).world.accounts b).code with
      | some _ => ((s.2.ex.apply p.sourceOp).world.accounts b).balance
      | none => G.fixed.ledger G.balance0 s.2.events b) = _
    rw [code,balance]
    rfl
  · rw [packedSourceStep_static F p s r static]

theorem packedSourceStep_observed_funds {E Γ ps ts}
    (G : Source.Glob E) (F : Source.Fr) (p : @PackedSlotPlan E.layout E.lay E.lay ps ts)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :
    sourceObservedFunds G (packedSourceStep F p s r).1.2 = sourceObservedFunds G s := by
  funext address
  exact congrArg environmentWord (packedSourceStep_observed_balance G F p s r (sourceAddressOfEnvironment address))

theorem packedSourceStep_target_funds {E Γ ps ts}
    (G : Source.Glob E) (F : Source.Fr) (p : @PackedSlotPlan E.layout E.lay E.lay ps ts)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :
    sourceEnvironmentFrame G F (sourceObservedFunds G (packedSourceStep F p s r).1.2) =
      sourceEnvironmentFrame G F (sourceObservedFunds G s) := by
  rw [packedSourceStep_observed_funds]

end Solidity.Yul.Views
