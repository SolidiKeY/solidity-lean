import Solidity.Evm.MemoryRecursiveCompile

namespace Solidity.Evm.Memory.Recursive
variable {C : Contract}

mutual
private def stmtallocatesM {b Γ Δ F G s code} : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code → Bool
  | .base cert => cert.allocates
  | .block cert => (progallocatesM cert)
  | .ite _ yes no => (progallocatesM yes) || (progallocatesM no)
  | .loop _ _ cert _ => (progallocatesM cert)
termination_by structural hs => hs
private def progallocatesM {b Γ Δ F G P code} : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code → Bool
  | .nil _ => false
  | .cons hs hp => (stmtallocatesM hs) || (progallocatesM hp)
termination_by structural hp => hp
end

@[implemented_by stmtallocatesM]
def StmtCert.allocates {b Γ Δ F G s code} (hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code) : Bool := by
  induction hs using StmtCert.rec (motive_2 := fun F G x code _=>Bool) with
  | base cert=>exact cert.allocates
  | @block Γ Δ F G body code cert ih=>exact ih
  | @ite Γ Δ Ξ F G K c yes no cond lc rc hc ht he iht ihe=>exact iht || ihe
  | @loop Γ Δ F G c body cond code a hc cert stable ih=>exact ih
  | @nil Γ F=>exact false
  | cons hs hp ihs ihp=>exact ihs || ihp

@[implemented_by progallocatesM]
def ProgCert.allocates {b Γ Δ F G P code} (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code) : Bool := by
  induction hp using ProgCert.rec (motive_1 := fun F G x code _=>Bool) with
  | base cert=>exact cert.allocates
  | @block Γ Δ F G body code cert ih=>exact ih
  | @ite Γ Δ Ξ F G K c yes no cond lc rc hc ht he iht ihe=>exact iht || ihe
  | @loop Γ Δ F G c body cond code a hc cert stable ih=>exact ih
  | @nil Γ F=>exact false
  | cons hs hp ihs ihp=>exact ihs || ihp

private theorem stmtallocates_eq {b Γ Δ F G s code} (hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code) :
    hs.allocates=stmtallocatesM hs := by
  induction hs using StmtCert.rec
    (motive_2 := fun F G P code cert=>cert.allocates=progallocatesM cert) with
  | base cert=>rfl
  | block cert ih=>exact ih
  | ite hc ht he iht ihe=>change (ht.allocates || he.allocates)=(progallocatesM ht || progallocatesM he);rw [iht,ihe]
  | loop a hc cert stable ih=>exact ih
  | nil F=>rfl
  | cons hs hp ihs ihp=>change (hs.allocates || hp.allocates)=(stmtallocatesM hs || progallocatesM hp);rw [ihs,ihp]

private theorem progallocates_eq {b Γ Δ F G P code} (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code) :
    hp.allocates=progallocatesM hp := by
  induction hp using ProgCert.rec
    (motive_1 := fun F G s code cert=>cert.allocates=stmtallocatesM cert) with
  | base cert=>rfl
  | block cert ih=>exact ih
  | ite hc ht he iht ihe=>change (ht.allocates || he.allocates)=(progallocatesM ht || progallocatesM he);rw [iht,ihe]
  | loop a hc cert stable ih=>exact ih
  | nil F=>rfl
  | cons hs hp ihs ihp=>change (hs.allocates || hp.allocates)=(stmtallocatesM hs || progallocatesM hp);rw [ihs,ihp]


private theorem scope_cost_zero {b Γ Δ F G s code}
    {old : LoopScopes.StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code}
    {σ : State C Γ} {out amount} (cost : LoopScopes.StmtCost old σ out amount)
    (run : s.run σ=.ok out) (none : old.allocates=false) : amount=0 := by
  let single := LoopScopes.ProgCert.cons old (.nil _)
  have oldCost : LoopScopes.Cost single σ out amount := by
    simpa only [Nat.add_zero] using LoopScopes.Cost.cons run cost (LoopScopes.Cost.nil out.st)
  have flags : single.allocates=false := by
    change (old.allocates || false)=false
    rw [none]
    rfl
  exact LoopScopes.cost_nonallocating oldCost flags

private theorem scope_demand_zero {b Γ Δ F G s code}
    {old : LoopScopes.StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code}
    {σ : State C Γ} {amount} (demand : LoopScopes.StmtDemand old σ amount)
    (none : old.allocates=false) : amount=0 := by
  let single := LoopScopes.ProgCert.cons old (.nil _)
  have flags : single.allocates=false := by
    change (old.allocates || false)=false
    rw [none]
    rfl
  exact LoopScopes.demand_nonallocating single flags (.head demand)

theorem StmtCost.nonallocating {b Γ Δ F G s code}
    {hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code}
    {σ : State C Γ} {out amount} (cost : StmtCost hs σ out amount)
    (run : s.run σ=.ok out) (none : hs.allocates=false) : amount=0 := by
  exact (StmtCost.rec
    (motive_1 := fun {Γ Δ F G s code} hs σ out amount _=>s.run σ=.ok out → hs.allocates=false → amount=0)
    (motive_2 := fun {Γ Δ F G P code} hp σ out amount _=>hp.allocates=false → amount=0)
    (motive_3 := fun {Γ Δ F G body code} hp c σ out amount _=>hp.allocates=false → amount=0)
    (fun oldCost=>by simpa only [StmtCert.allocates] using scope_cost_zero oldCost)
    (fun run cost ih=>by intro _ none;exact ih none)
    (fun condition run cost ih=>by intro _ none;exact ih (Bool.or_eq_false_iff.mp none).1)
    (fun condition run cost ih=>by intro _ none;exact ih (Bool.or_eq_false_iff.mp none).2)
    (fun hpref ih=>by intro _ none;exact ih none)
    (fun σ=>by intro none;rfl)
    (fun run cost rest ihs iht=>by
      intro none
      have flags:=Bool.or_eq_false_iff.mp none
      rw [ihs run flags.1,iht flags.2])
    (fun cert c σ=>by intro none;rfl)
    (fun before condition run spent ihp ihb=>by intro none;rw [ihp none,ihb none])
    cost) run none

theorem Cost.nonallocating {b Γ Δ F G P code}
    {hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code}
    {σ : State C Γ} {out amount} (cost : Cost hp σ out amount) (none : hp.allocates=false) : amount=0 := by
  exact (Cost.rec
    (motive_1 := fun {Γ Δ F G s code} hs σ out amount _=>s.run σ=.ok out → hs.allocates=false → amount=0)
    (motive_2 := fun {Γ Δ F G P code} hp σ out amount _=>hp.allocates=false → amount=0)
    (motive_3 := fun {Γ Δ F G body code} hp c σ out amount _=>hp.allocates=false → amount=0)
    (fun oldCost=>by simpa only [StmtCert.allocates] using scope_cost_zero oldCost)
    (fun run cost ih=>by intro _ none;exact ih none)
    (fun condition run cost ih=>by intro _ none;exact ih (Bool.or_eq_false_iff.mp none).1)
    (fun condition run cost ih=>by intro _ none;exact ih (Bool.or_eq_false_iff.mp none).2)
    (fun hpref ih=>by intro _ none;exact ih none)
    (fun σ=>by intro none;rfl)
    (fun run cost rest ihs iht=>by
      intro none
      have flags:=Bool.or_eq_false_iff.mp none
      rw [ihs run flags.1,iht flags.2])
    (fun cert c σ=>by intro none;rfl)
    (fun before condition run spent ihp ihb=>by intro none;rw [ihp none,ihb none])
    cost) none

theorem LoopPrefix.nonallocating {b Γ Δ F G body code}
    {hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G body code} {c : Val C Γ .bool}
    {σ : State C Γ} {out amount} (cost : LoopPrefix hp c σ out amount) (none : hp.allocates=false) : amount=0 := by
  exact (LoopPrefix.rec
    (motive_1 := fun {Γ Δ F G s code} hs σ out amount _=>s.run σ=.ok out → hs.allocates=false → amount=0)
    (motive_2 := fun {Γ Δ F G P code} hp σ out amount _=>hp.allocates=false → amount=0)
    (motive_3 := fun {Γ Δ F G body code} hp c σ out amount _=>hp.allocates=false → amount=0)
    (fun oldCost=>by simpa only [StmtCert.allocates] using scope_cost_zero oldCost)
    (fun run cost ih=>by intro _ none;exact ih none)
    (fun condition run cost ih=>by intro _ none;exact ih (Bool.or_eq_false_iff.mp none).1)
    (fun condition run cost ih=>by intro _ none;exact ih (Bool.or_eq_false_iff.mp none).2)
    (fun hpref ih=>by intro _ none;exact ih none)
    (fun σ=>by intro none;rfl)
    (fun run cost rest ihs iht=>by
      intro none
      have flags:=Bool.or_eq_false_iff.mp none
      rw [ihs run flags.1,iht flags.2])
    (fun cert c σ=>by intro none;rfl)
    (fun before condition run spent ihp ihb=>by intro none;rw [ihp none,ihb none])
    cost) none

theorem StmtDemand.nonallocating {b Γ Δ F G s code}
    {hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code}
    {σ : State C Γ} {amount} (demand : StmtDemand hs σ amount) (none : hs.allocates=false) : amount=0 := by
  exact (StmtDemand.rec
    (motive_1 := fun {Γ Δ F G s code} hs σ amount _=>hs.allocates=false → amount=0)
    (motive_2 := fun {Γ Δ F G P code} hp σ amount _=>hp.allocates=false → amount=0)
    (fun oldDemand=>by simpa only [StmtCert.allocates] using scope_demand_zero oldDemand)
    (fun inner ih=>by intro none;exact ih none)
    (fun condition inner ih=>by intro none;exact ih (Bool.or_eq_false_iff.mp none).1)
    (fun condition inner ih=>by intro none;exact ih (Bool.or_eq_false_iff.mp none).2)
    (fun hp=>by intro none;exact hp.nonallocating none)
    (fun hp condition inner ih=>by intro none;rw [hp.nonallocating none,ih none])
    (fun inner ih=>by intro none;exact ih (Bool.or_eq_false_iff.mp none).1)
    (fun run cost inner ih=>by
      intro none
      have flags:=Bool.or_eq_false_iff.mp none
      rw [cost.nonallocating run flags.1,ih flags.2])
    demand) none

theorem Demand.nonallocating {b Γ Δ F G P code}
    {hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code}
    {σ : State C Γ} {amount} (demand : Demand hp σ amount) (none : hp.allocates=false) : amount=0 := by
  exact (Demand.rec
    (motive_1 := fun {Γ Δ F G s code} hs σ amount _=>hs.allocates=false → amount=0)
    (motive_2 := fun {Γ Δ F G P code} hp σ amount _=>hp.allocates=false → amount=0)
    (fun oldDemand=>by simpa only [StmtCert.allocates] using scope_demand_zero oldDemand)
    (fun inner ih=>by intro none;exact ih none)
    (fun condition inner ih=>by intro none;exact ih (Bool.or_eq_false_iff.mp none).1)
    (fun condition inner ih=>by intro none;exact ih (Bool.or_eq_false_iff.mp none).2)
    (fun hp=>by intro none;exact hp.nonallocating none)
    (fun hp condition inner ih=>by intro none;rw [hp.nonallocating none,ih none])
    (fun inner ih=>by intro none;exact ih (Bool.or_eq_false_iff.mp none).1)
    (fun run cost inner ih=>by
      intro none
      have flags:=Bool.or_eq_false_iff.mp none
      rw [cost.nonallocating run flags.1,ih flags.2])
    demand) none

theorem room_nonallocating {b Γ Δ F G P code}
    (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code) (none : hp.allocates=false)
    (frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Room hp frame σ base m :=
  fun _ demand=>.inl (demand.nonallocating none)

end Solidity.Evm.Memory.Recursive
