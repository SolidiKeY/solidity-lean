import Solidity.Evm.MemoryRecursiveRoom
import Solidity.Evm.MemoryRecursiveFinite

namespace Solidity.Evm.Memory.Recursive
variable {C : Contract}

/-- Public all-depth loop horizon transport. Body soundness is derived from
its actual recursive certificate, not an additional producer premise. -/
theorem ProgCert.loop_horizon {b L frame Γ Δ F G c body cond code}
    (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G body code)
    (hc : ValFrag b F c cond) (stable : G.restrict Γ=F)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (cap : b+hp.need≤frame)
    (room : RecursiveLift.Room (loopKit hc hp stable) frame σ base m) (n : Nat) :
    RecursiveLift.Horizon (loopKit hc hp stable) L frame σ base m
      (TLoop.iterN (horizonBody body) (fun o=>c.evalT o.st) n ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m=>exec cond 0 m) (fun m=>exec code 0 m) n m) :=
  (loopKit hc hp stable).correct_horizon hp.profile_sound repr cap room n

/-- Nonallocating metadata discharges every real reached allocation demand,
including arbitrarily many successful prefixes and inner divergence. -/
theorem loop_room_nonallocating {b Γ Δ F G c body cond code}
    (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G body code)
    (hc : ValFrag b F c cond) (stable : G.restrict Γ=F) (none : hp.allocates=false)
    (frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) :
    RecursiveLift.Room (loopKit hc hp stable) frame σ base m := by
  intro out amount before condition spent demand
  have prefixZero := (LoopPrefix.ofLift before).nonallocating none
  have demandZero := demand.nonallocating none
  exact .inl (by rw [prefixZero,demandZero])

/-- Only demands reached before the supplied outer horizon are required.
No blanket room premise for later iterations is introduced. -/
theorem ProgCert.loop_finite_horizon {b L frame Γ Δ F G c body cond code}
    (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G body code)
    (hc : ValFrag b F c cond) (stable : G.restrict Γ=F)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base m) (cap : b+hp.need≤frame)
    (room : RecursiveLift.FiniteRoom (loopKit hc hp stable) frame σ base m n) :
    RecursiveLift.CountedHorizon (loopKit hc hp stable) L frame σ base m n
      (TLoop.iterN (horizonBody body) (fun o=>c.evalT o.st) n ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m=>exec cond 0 m) (fun m=>exec code 0 m) n m) :=
  (loopKit hc hp stable).correct_finite_horizon hp.profile_sound n repr cap room

end Solidity.Evm.Memory.Recursive
