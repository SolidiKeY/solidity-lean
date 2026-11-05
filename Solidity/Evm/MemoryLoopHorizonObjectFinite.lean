import Solidity.Evm.MemoryLoopHorizonObjectStep

/-! Finite iteration for the complete-object construction compiler. Pending
observations retain exact successful-turn counts; completed observations carry
a real false condition and a smaller count. Only reached true-condition turns
before the requested horizon require complete allocator room. This assumes
owner certificates explicitly and proves no Source adequacy or full compiler
selection closure. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

inductive CountedHorizonRelation (L b frame : Nat) (F : Frag Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Δ) (σ : State C Γ) (base : Nat → Fin W) (m₀ : Machine) (turns : Nat) :
    Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ) → Machine ⊕ Out → Prop where
  | more {o m base' cost} (hpref : CountedLoopPrefix c body σ o cost turns)
      (repr : Objects.StateRepr L b frame F o.st base' m) (stack : m.stack = m₀.stack)
      (hbase : BaseExtends σ.H base base')
      (grows : Objects.GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      CountedHorizonRelation L b frame F c body σ base m₀ turns (.inl o) (.inl m)
  | done {o m base' cost count} (hpref : CountedLoopPrefix c body σ o cost count)
      (earlier : count < turns) (stopped : c.evalT o.st = .ok false)
      (repr : Objects.StateRepr L b frame F o.st base' m) (stack : m.stack = m₀.stack)
      (hbase : BaseExtends σ.H base base')
      (grows : Objects.GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      CountedHorizonRelation L b frame F c body σ base m₀ turns (.inr (.ok o)) (.inr (.ok m 0))
  | revert : CountedHorizonRelation L b frame F c body σ base m₀ turns
      (.inr (.error .revert)) (.inr .revert)

theorem CountedHorizonRelation.forget {L b frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {turns : Nat} {source : Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ)}
    {target : Machine ⊕ Out}
    (h : CountedHorizonRelation L b frame F c body σ base m turns source target) :
    HorizonRelation L b frame F c body σ base m source target := by
  cases h with
  | more hp hr hs he hg => exact .more hp hr hs he hg
  | done hp _ _ hr hs he hg => exact .done hp hr hs he hg
  | revert => exact .revert

/-- One actual condition/body turn, including condition and body reverts. -/
theorem LoopCert.finite_horizon_step {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (cap : b + frameNeedProg body ≤ frame)
    {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost turns : Nat}
    (hpref : CountedLoopPrefix c body σ o cost turns)
    (room : c.evalT o.st = .ok true →
      Objects.AllocationInput b frame (cost + allocationCostProg body o.st) σ base m₀)
    (repr : Objects.StateRepr L b frame F o.st base' m)
    (stack : m.stack = m₀.stack) (hbase : BaseExtends σ.H base base')
    (grows : Objects.GrowsAllocator b frame cost σ base m₀ o.st base' m) :
    CountedHorizonRelation L b frame F c body σ base m₀ (turns + 1)
      (TLoop.step (horizonBody body) (fun o => c.evalT o.st) o)
      (loopTurn (fun m => exec cond 0 m) (fun m => exec code 0 m) m) := by
  rcases cert.condition.correct repr with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · obtain rfl := hw.bool_inv
    have hc' : exec cond 0 m = .ok (m.push (.val (bword v))) 0 := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv, hc']
    cases v
    · exact .done hpref (Nat.lt_succ_self turns) hv repr stack hbase grows
    · change CountedHorizonRelation L b frame F c body σ base m₀ (turns + 1) _
        (match exec code 0 m with
          | .ok m₂ 0 => .inl m₂
          | .ok _ (_ + 1) => .inr .fault
          | r => .inr r)
      have ha : Objects.AllocationInput b frame (allocationCostProg body o.st) o.st base' m :=
        grows.nextInput (room hv)
      rcases cert.bodyCert.correct repr cap ha with
        ⟨o', m', base'', ho, ht, hr, hs, he, hg⟩ | ⟨ho, ht⟩
      · have ht' : exec code 0 m = .ok m' 0 := ht
        simp only [horizonBody, ho, Except.map, ht']
        refine .more (.next hpref hv ho) ?_ (hs.trans stack) (hbase.trans o.ext he) ?_
        · rw [← cert.stable]
          exact hr.drop body.ext
        · exact grows.comp hg
      · have ht' : exec code 0 m = .revert := ht
        simp only [horizonBody, ho, Except.map, ht']
        exact .revert
  · have hc' : exec cond 0 m = .revert := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv, hc']
    exact .revert

/-- Transport with room only for reached turns strictly before the finite
budget. Current successful-turn count plus remaining horizon cannot exceed it. -/
theorem LoopCert.finite_horizon_iter {b L frame horizon : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (room : FiniteLoopRoom b frame c body σ base m₀ horizon)
    (cap : b + frameNeedProg body ≤ frame) :
    ∀ n (turns : Nat), turns + n ≤ horizon →
      ∀ {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost : Nat},
      CountedLoopPrefix c body σ o cost turns → Objects.StateRepr L b frame F o.st base' m →
      m.stack = m₀.stack → BaseExtends σ.H base base' →
      Objects.GrowsAllocator b frame cost σ base m₀ o.st base' m →
      CountedHorizonRelation L b frame F c body σ base m₀ (turns + n)
        (TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n o)
        (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n m)
  | 0, _, _, _, _, _, _, hp, hr, hs, he, hg => .more hp hr hs he hg
  | n + 1, turns, hbudget, _, _, _, _, hp, hr, hs, he, hg => by
    have ht := cert.finite_horizon_step cap hp
      (fun hc => room _ _ turns hp (by omega) hc) hr hs he hg
    simp only [TLoop.iterN, loopIterN]
    revert ht
    generalize TLoop.step _ _ _ = A
    generalize loopTurn _ _ _ = B
    intro ht
    cases ht with
    | more hp hr hs he hg =>
      have h := LoopCert.finite_horizon_iter cert room cap n (turns + 1) (by omega) hp hr hs he hg
      simpa only [Nat.succ_add, Nat.add_succ] using h
    | done hp hcount hstop hr hs he hg => exact .done hp (by omega) hstop hr hs he hg
    | revert => exact .revert

/-- Public finite-only allocation interface. No room is required for the next
turn after the requested horizon, including horizon zero. -/
theorem LoopCert.correct_finite_horizon {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (n : Nat) (repr : Objects.StateRepr L b frame F σ base m)
    (cap : b + frameNeedProg body ≤ frame)
    (room : FiniteLoopRoom b frame c body σ base m n) :
    CountedHorizonRelation L b frame F c body σ base m n
      (TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ, List.prefix_refl _⟩)
      (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n m) := by
  simpa only [Nat.zero_add] using
    (cert.finite_horizon_iter room cap n 0 (by omega) .start repr rfl
      (BaseExtends.refl base) (fun _ _ ha _ => ha))

end Solidity.Evm.Memory.Construction
