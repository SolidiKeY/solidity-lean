import Solidity.Evm.MemoryLoopScopeRoom
namespace Solidity.Evm.Memory.LoopScopes
variable {C : Contract}

/-- One layer of reached demand, exposed without inverting computed fragment indices. -/
def StmtDemandView {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    (σ : State C Γ) (amount : Nat) : Prop :=
  StmtCert.casesOn
    (motive_1 := fun {Γ Δ} F G s code hs => State C Γ → Nat → Prop) hs
    (fun cert σ amount => Loops.Demand (singleton cert) σ amount)
    (fun hp σ amount => Demand hp σ amount)
    (fun {Γ Δ Ξ F G K c thn els cond left right} hc ht he σ amount =>
      (c.evalT σ = .ok true ∧ Demand ht σ amount) ∨
      (c.evalT σ = .ok false ∧ Demand he σ amount)) σ amount

def DemandView {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (σ : State C Γ) (amount : Nat) : Prop :=
  ProgCert.casesOn
    (motive_2 := fun {Γ Δ} F G P code hp => State C Γ → Nat → Prop) hp
    (fun _ _ _ => False)
    (fun {Γ Δ Ξ F G K s P head tail} hs ht σ amount => StmtDemand hs σ amount ∨
      ∃ o cost rest, s.run σ = Except.ok o ∧ StmtCost hs σ o cost ∧
        Demand ht o.st rest ∧ amount = cost + rest) σ amount

theorem StmtDemand.view {b Γ Δ F G s code}
    {hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code}
    {σ : State C Γ} {amount} (hd : StmtDemand hs σ amount) : StmtDemandView hs σ amount := by
  induction hd using StmtDemand.rec
    (motive_2 := fun {Γ Δ F G P code} hp σ amount _ => DemandView hp σ amount) with
  | base hd => exact hd
  | block hd ih => exact hd
  | iteTrue hv hd ih => exact .inl ⟨hv, hd⟩
  | iteFalse hv hd ih => exact .inr ⟨hv, hd⟩
  | head hd ih => exact .inl hd
  | tail ho hc hd ih => exact .inr ⟨_, _, _, ho, hc, hd, rfl⟩

theorem Demand.view {b Γ Δ F G P code}
    {hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code}
    {σ : State C Γ} {amount} (hd : Demand hp σ amount) : DemandView hp σ amount := by
  induction hd using Demand.rec
    (motive_1 := fun {Γ Δ F G s code} hs σ amount _ => StmtDemandView hs σ amount) with
  | base hd => exact hd
  | block hd ih => exact hd
  | iteTrue hv hd ih => exact .inl ⟨hv, hd⟩
  | iteFalse hv hd ih => exact .inr ⟨hv, hd⟩
  | head hd ih => exact .inl hd
  | tail ho hc hd ih => exact .inr ⟨_, _, _, ho, hc, hd, rfl⟩


/-- The base statement keeps the exact legacy singleton cost proof. -/
def StmtCostView {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    (σ : State C Γ) (o : Solidity.Out C σ.H Δ) (amount : Nat) : Prop :=
  StmtCert.casesOn
    (motive_1 := fun {Γ Δ} F G s code hs =>
      (σ : State C Γ) → Solidity.Out C σ.H Δ → Nat → Prop) hs
    (fun cert σ o amount => Loops.Cost (singleton cert) σ o amount)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ _ _ => True) σ o amount

theorem StmtCost.view {b Γ Δ F G s code}
    {hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code}
    {σ : State C Γ} {o amount} (hc : StmtCost hs σ o amount) : StmtCostView hs σ o amount := by
  induction hc using StmtCost.rec
    (motive_2 := fun {Γ Δ F G P code} hp σ o amount _ => True) with
  | base hc => exact hc
  | block => trivial
  | iteTrue => trivial
  | iteFalse => trivial
  | nil => trivial
  | cons => trivial

/-- Scope composition needs no capacity for an unreachable continuation. -/
theorem room_block {b frame Γ Δ F G body code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G body code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (room : Room hp frame σ base m) :
    Room (.cons (.block hp) (.nil (G.restrict Γ))) frame σ base m := by
  intro amount hd
  rcases hd.view with hd | ⟨o, cost, rest, ho, hc, hd, he⟩
  · exact room amount hd.view
  · exact hd.view.elim

theorem room_ite_true {b frame Γ Δ Ξ F G K thn els cond left right} {c : Val C Γ .bool}
    (hc : ValFrag (C := C) b (Γ := Γ) F c cond)
    (ht : ProgCert b (Γ := Γ) (Δ := Δ) F G thn left)
    (he : ProgCert b (Γ := Γ) (Δ := Ξ) F K els right)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (hv : c.evalT σ = .ok true) (room : Room ht frame σ base m) :
    Room (.cons (.ite hc ht he) (.nil _)) frame σ base m := by
  intro amount hd
  rcases hd.view with hd | ⟨o, cost, rest, ho, hc, hd, hsum⟩
  · rcases hd.view with ⟨hv', hd⟩ | ⟨hv', hd⟩
    · exact room amount hd
    · rw [hv] at hv'
      cases hv'
  · exact hd.view.elim

theorem room_ite_false {b frame Γ Δ Ξ F G K thn els cond left right} {c : Val C Γ .bool}
    (hc : ValFrag (C := C) b (Γ := Γ) F c cond)
    (ht : ProgCert b (Γ := Γ) (Δ := Δ) F G thn left)
    (he : ProgCert b (Γ := Γ) (Δ := Ξ) F K els right)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (hv : c.evalT σ = .ok false) (room : Room he frame σ base m) :
    Room (.cons (.ite hc ht he) (.nil _)) frame σ base m := by
  intro amount hd
  rcases hd.view with hd | ⟨o, cost, rest, ho, hc, hd, hsum⟩
  · rcases hd.view with ⟨hv', hd⟩ | ⟨hv', hd⟩
    · rw [hv] at hv'
      cases hv'
    · exact room amount hd
  · exact hd.view.elim


/-- A legacy loop statement retains its exact reached-prefix room in a scope. -/
theorem room_base_singleton {b frame Γ Δ F G s code}
    (hs : Loops.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (room : Loops.Room (singleton hs) frame σ base m) :
    Room (.cons (.base hs) (.nil G)) frame σ base m := by
  intro amount hd
  rcases hd.view with hd | ⟨o, cost, rest, ho, hc, hd, he⟩
  · exact room amount hd.view
  · exact hd.view.elim

end Solidity.Evm.Memory.LoopScopes
