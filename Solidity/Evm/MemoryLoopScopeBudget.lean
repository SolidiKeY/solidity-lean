import Solidity.Evm.MemoryLoopScopeDemand
namespace Solidity.Evm.Memory.LoopScopes
variable {C : Contract}

private def OldCostView {b Γ Δ F G P code}
    (hp : Loops.ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (σ : State C Γ) (amount : Nat) : Prop :=
  Loops.ProgCert.casesOn
    (motive := fun {Γ Δ} F G P code hp => State C Γ → Nat → Prop) hp
    (fun _ _ amount => amount = 0)
    (fun hs ht σ amount => ∃ o cost rest o',
      Loops.StmtCert.Cost hs σ o cost ∧ Loops.Cost ht o.st o' rest ∧ amount = cost + rest) σ amount

private theorem old_cost_view {b Γ Δ F G P code}
    {hp : Loops.ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code}
    {σ : State C Γ} {o amount} (hc : Loops.Cost hp σ o amount) : OldCostView hp σ amount := by
  induction hc with
  | nil => rfl
  | cons ho hc ht ih => exact ⟨_, _, _, _, hc, ht, rfl⟩

private theorem singleton_finite_cost {b Γ Δ F G s code}
    (hs : StmtFrag (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    {σ : State C Γ} {o amount} (hc : Loops.Cost (singleton (.finite hs)) σ o amount) :
    amount = allocationCostStmt s σ := by
  rcases old_cost_view hc with ⟨mid, cost, rest, last, hsCost, tailCost, hsum⟩
  have hz : rest = 0 := old_cost_view tailCost
  change cost = allocationCostStmt s σ at hsCost
  rw [hsum, hsCost, hz, Nat.add_zero]

private def finiteBudget {b Γ Δ F G s code}
    (hs : Loops.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    (rest : State C Δ → Option Nat) (allocates : Bool) (σ : State C Γ) : Option Nat :=
  Loops.StmtCert.casesOn
    (motive := fun {Δ} F G s code hs =>
      (State C Δ → Option Nat) → Bool → State C Γ → Option Nat) hs
    (fun {_ _ _ s _} _ rest allocates σ =>
      if allocates then
        match s.run σ with
        | .ok o => (rest o.st).map (allocationCostStmt s σ + ·)
        | .error _ => some (allocationCostStmt s σ)
      else some (allocationCostStmt s σ))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => none) rest allocates σ

/-- Recognize a finite allocating prefix, then stop before any nonallocating scope.
No possibly diverging loop or unselected branch is evaluated by this recognizer. -/
def prefixBudget {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (σ : State C Γ) : Option Nat :=
  ProgCert.casesOn
    (motive_2 := fun {Γ Δ} F G P code hp => State C Γ → Option Nat) hp
    (fun _ _ => some 0)
    (fun {Γ Δ Ξ F G K s P head tail} hs ht σ =>
      StmtCert.casesOn
        (motive_1 := fun {Γ Δ} F G s code hs =>
          (State C Δ → Option Nat) → Bool → State C Γ → Option Nat) hs
        (fun hs => finiteBudget hs)
        (fun _ _ _ _ => none)
        (fun _ _ _ _ _ _ => none)
        (prefixBudget ht) ht.allocates σ) σ
termination_by structural hp

theorem demand_le_prefixBudget {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    {σ : State C Γ} {budget amount}
    (hb : prefixBudget hp σ = some budget) (hd : Demand hp σ amount) : amount ≤ budget := by
  induction hp using ProgCert.rec
    (motive_1 := fun F G s code hs => True) generalizing budget amount with
  | base => trivial
  | block => trivial
  | ite => trivial
  | nil F => exact hd.view.elim
  | @cons Γ Δ Ξ F G K s P head tail hs ht ihs ih =>
    cases hs with
    | block => change none = some budget at hb; cases hb
    | ite => change none = some budget at hb; cases hb
    | base hs =>
      cases hs with
      | loop => change none = some budget at hb; cases hb
      | finite cert =>
        change (if ht.allocates then
          match s.run σ with
          | .ok o => (prefixBudget ht o.st).map (allocationCostStmt s σ + ·)
          | .error _ => some (allocationCostStmt s σ)
          else some (allocationCostStmt s σ)) = some budget at hb
        cases hn : ht.allocates with
        | false =>
          simp only [hn, Bool.false_eq_true, if_false] at hb
          cases hb
          rcases hd.view with hd | ⟨o, cost, rest, ho, hc, hrest, rfl⟩
          · have h := hd.view
            rcases h with h | ⟨o, cost, rest, ho, hc, hd, he⟩
            · exact h ▸ Nat.le_refl _
            · exact hd.elim
          · rw [singleton_finite_cost cert hc.view, demand_nonallocating ht hn hrest, Nat.add_zero]
            exact Nat.le_refl _
        | true =>
          simp only [hn, if_true] at hb
          cases hsrun : s.run σ with
          | error halt =>
            simp only [hsrun] at hb
            cases hb
            rcases hd.view with hd | ⟨o, cost, rest, ho, hc, hd, he⟩
            · have h := hd.view
              rcases h with h | ⟨o, cost, rest, ho, hc, hd, he⟩
              · exact h ▸ Nat.le_refl _
              · exact hd.elim
            · rw [hsrun] at ho
              cases ho
          | ok out =>
            simp only [hsrun] at hb
            cases htbudget : prefixBudget ht out.st with
            | none => rw [htbudget] at hb; cases hb
            | some restBudget =>
              rw [htbudget] at hb
              cases hb
              rcases hd.view with hd | ⟨o, cost, rest, ho, hc, hrest, rfl⟩
              · have h := hd.view
                rcases h with h | ⟨o, cost, rest, ho, hc, hd, he⟩
                · rw [h]; exact Nat.le_add_right _ _
                · exact hd.elim
              · have he : o = out := Except.ok.inj (ho.symm.trans hsrun)
                subst o
                rw [singleton_finite_cost cert hc.view]
                exact Nat.add_le_add_left (ih htbudget hrest) _

theorem room_of_prefixBudget {b frame Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {budget}
    (hb : prefixBudget hp σ = some budget) (ha : AllocationInput b frame budget σ base m) :
    Room hp frame σ base m := fun _ hd => ha.of_le (demand_le_prefixBudget hp hb hd)


/-- Every successful base-statement cost is already a reached singleton demand. -/
theorem base_success_demand {b Γ Δ F G s code}
    (hs : Loops.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    {σ : State C Γ} {o amount} (hc : StmtCost (.base hs) σ o amount) :
    Loops.Demand (singleton hs) σ amount := by
  rcases old_cost_view hc.view with ⟨mid, cost, rest, last, hcost, htail, hsum⟩
  have hz : rest = 0 := old_cost_view htail
  rw [hz, Nat.add_zero] at hsum
  subst amount
  cases hs with
  | finite cert => exact Loops.Demand.head hcost
  | loop a c body cond code G hv hb stable => exact Loops.Demand.head (.inl ⟨mid, hcost⟩)

/-- A reached base loop/statement can precede a nonallocating scope, including divergence. -/
theorem room_cons_base_nonallocating {b frame Γ Δ Ξ F G K s P head tail}
    (hs : Loops.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s head)
    (hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail)
    (hn : hp.allocates = false)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (room : Loops.Room (singleton hs) frame σ base m) :
    Room (.cons (.base hs) hp) frame σ base m := by
  intro amount hd
  rcases hd.view with hhead | ⟨o, cost, rest, ho, hc, hrest, rfl⟩
  · exact room amount hhead.view
  · rw [demand_nonallocating hp hn hrest, Nat.add_zero]
    exact room cost (base_success_demand hs hc)

end Solidity.Evm.Memory.LoopScopes
