import Solidity.Evm.MemoryLoopScopeSound
namespace Solidity.Evm.Memory.LoopScopes
variable {C : Contract}

private theorem old_stmt_cost_zero {b Γ Δ F G s code}
    (hs : Loops.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    {σ : State C Γ} {o : Solidity.Out C σ.H Δ} {amount}
    (hn : hs.allocates = false) (hc : hs.Cost σ o amount) : amount = 0 := by
  cases hs with
  | finite cert =>
    rw [hc]
    simp only [allocationCostStmt, show hasAllocationStmt s = false from hn, Bool.false_eq_true, if_false]
  | loop a c body cond code G hv hb stable => exact hc.cost_zero hn

private theorem old_cost_zero {b Γ Δ F G P code}
    (hp : Loops.ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    {σ : State C Γ} {o : Solidity.Out C σ.H Δ} {amount}
    (hn : hp.allocates = false) (hc : Loops.Cost hp σ o amount) : amount = 0 := by
  induction hc with
  | nil => rfl
  | cons ho hc ht ih =>
    have h := Bool.or_eq_false_iff.mp hn
    rw [old_stmt_cost_zero _ h.1 hc, ih h.2]


theorem cost_nonallocating {b Γ Δ F G P code}
    {hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code}
    {σ : State C Γ} {o amount} (hc : Cost hp σ o amount)
    (hn : hp.allocates = false) : amount = 0 := by
  induction hc using Cost.rec
    (motive_1 := fun {Γ Δ F G s code} hs σ o amount _ => hs.allocates = false → amount = 0) with
  | base hc => rename_i hn; exact old_cost_zero _ hn hc
  | block ho hc ih => rename_i hn; exact ih hn
  | iteTrue hv ho hc ih => rename_i hn; exact ih (Bool.or_eq_false_iff.mp hn).1
  | iteFalse hv ho hc ih => rename_i hn; exact ih (Bool.or_eq_false_iff.mp hn).2
  | nil => rfl
  | cons ho hc ht ihs iht =>
    have h := Bool.or_eq_false_iff.mp hn
    rw [ihs h.1, iht h.2]

private theorem stmt_cost_nonallocating {b Γ Δ F G s code}
    {hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code}
    {σ : State C Γ} {o amount} (hc : StmtCost hs σ o amount)
    (hn : hs.allocates = false) : amount = 0 := by
  induction hc using StmtCost.rec
    (motive_2 := fun {Γ Δ F G P code} hp σ o amount _ => hp.allocates = false → amount = 0) with
  | base hc => exact old_cost_zero _ hn hc
  | block ho hc ih => exact ih hn
  | iteTrue hv ho hc ih => exact ih (Bool.or_eq_false_iff.mp hn).1
  | iteFalse hv ho hc ih => exact ih (Bool.or_eq_false_iff.mp hn).2
  | nil => rename_i hn; rfl
  | cons ho hc ht ihs iht =>
    rename_i hn
    have h := Bool.or_eq_false_iff.mp hn
    rw [ihs h.1, iht h.2]

theorem demand_nonallocating {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (hn : hp.allocates = false) {σ : State C Γ} {amount}
    (hd : Demand hp σ amount) : amount = 0 := by
  induction hd using Demand.rec
    (motive_1 := fun {Γ Δ F G s code} hs σ amount _ => hs.allocates = false → amount = 0) with
  | base hd => rename_i hn; exact Loops.demand_nonallocating _ hn hd
  | block hd ih => rename_i hn; exact ih hn
  | iteTrue hv hd ih => rename_i hn; exact ih (Bool.or_eq_false_iff.mp hn).1
  | iteFalse hv hd ih => rename_i hn; exact ih (Bool.or_eq_false_iff.mp hn).2
  | head hd ih => exact ih (Bool.or_eq_false_iff.mp hn).1
  | tail ho hc hd ih =>
    have h := Bool.or_eq_false_iff.mp hn
    rw [stmt_cost_nonallocating hc h.1, ih h.2]

theorem room_nonallocating {b frame Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (hn : hp.allocates = false) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) :
    Room hp frame σ base m := fun _ hd => .inl (demand_nonallocating hp hn hd)

theorem ProgCert.not_exhausted {b L frame Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (hr : StateRepr L b frame F σ base m) (cap : b + hp.need ≤ frame)
    (room : Room hp frame σ base m) : P.run σ ≠ .error .exhausted := by
  rcases hp.correct σ base m hr cap room with ⟨o, _, _, _, ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ <;>
    rw [ho] <;> intro h <;> cases h

theorem StmtCert.pushes_zero {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) : Evm.Stmt.pushes s = 0 := by
  induction hs using StmtCert.rec
    (motive_2 := fun F G P code hp => Evm.Prog.pushes P = 0) with
  | base hs => exact hs.pushes_zero
  | block hp ih => exact ih
  | ite hc ht he iht ihe =>
    change Evm.Prog.pushes _ + Evm.Prog.pushes _ = 0
    rw [iht, ihe]
  | nil F => rfl
  | cons hs hp ihs ihp =>
    change Evm.Stmt.pushes _ + Evm.Prog.pushes _ = 0
    rw [ihs, ihp]

theorem ProgCert.pushes_zero {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) : Evm.Prog.pushes P = 0 := by
  induction hp using ProgCert.rec
    (motive_1 := fun F G s code hs => Evm.Stmt.pushes s = 0) with
  | base hs => exact hs.pushes_zero
  | block hp ih => exact ih
  | ite hc ht he iht ihe =>
    change Evm.Prog.pushes _ + Evm.Prog.pushes _ = 0
    rw [iht, ihe]
  | nil F => rfl
  | cons hs hp ihs ihp =>
    change Evm.Stmt.pushes _ + Evm.Prog.pushes _ = 0
    rw [ihs, ihp]

end Solidity.Evm.Memory.LoopScopes
