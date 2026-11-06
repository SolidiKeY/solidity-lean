import Solidity.Evm.MemoryLoopHorizon

/-! Finite-turn allocation demand over actual source prefixes, without requiring
capacity for unreachable turns beyond the requested horizon. Body execution is
still the owner's actual `body.run`, not recursive statement fuel. -/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

/-- Proof-only reached prefixes, adding the successful-body count to the
owner's exact source execution and allocation cost. -/
inductive CountedLoopPrefix (c : Val C Γ .bool) (body : Prog C Γ Δ) (σ : State C Γ) :
    Solidity.Out C σ.H Γ → Nat → Nat → Prop where
  | start : CountedLoopPrefix c body σ ⟨σ, List.prefix_refl _⟩ 0 0
  | next {o : Solidity.Out C σ.H Γ} {cost turns : Nat}
      {o' : Solidity.Out C o.st.H Δ}
      (hpref : CountedLoopPrefix c body σ o cost turns)
      (condition : c.evalT o.st = .ok true) (step : body.run o.st = .ok o') :
      CountedLoopPrefix c body σ ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩
        (cost + allocationCostProg body o.st) (turns + 1)

theorem CountedLoopPrefix.forget {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {o : Solidity.Out C σ.H Γ} {cost turns : Nat}
    (h : CountedLoopPrefix c body σ o cost turns) : LoopPrefix c body σ o cost := by
  induction h with
  | start => exact .start
  | next hp hc hs ih => exact .next ih hc hs

/-- Extending an actual pending iterator by one turn executes its actual step. -/
theorem iterN_succ_of_pending {α : Type} {f : α → TRes α} {c : α → TRes Bool}
    {n : Nat} {σ τ : α} (h : TLoop.iterN f c n σ = .inl τ) :
    TLoop.iterN f c (n + 1) σ = TLoop.step f c τ := by
  induction n generalizing σ with
  | zero =>
    cases h
    cases hs : TLoop.step f c τ <;> simp only [TLoop.iterN, hs]
  | succ n ih =>
    simp only [TLoop.iterN] at h ⊢
    cases hs : TLoop.step f c σ with
    | inl next =>
      rw [hs] at h
      exact ih h
    | inr result =>
      rw [hs] at h
      cases h

/-- Every counted prefix is the real source observation at that count. -/
theorem CountedLoopPrefix.iterN_eq {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {o : Solidity.Out C σ.H Γ} {cost turns : Nat}
    (h : CountedLoopPrefix c body σ o cost turns) :
    TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) turns
      ⟨σ, List.prefix_refl _⟩ = .inl o := by
  induction h with
  | start => rfl
  | next hp hc hs ih =>
    rw [iterN_succ_of_pending ih]
    simp only [TLoop.step, hc, horizonBody, hs, Except.map]

/-- Conversely, successful pending source iterations construct their exact
counted prefix and allocation cost; this is not an assumed trace coverage law. -/
theorem CountedLoopPrefix.extend_pending {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} :
    ∀ n {o : Solidity.Out C σ.H Γ} {cost turns : Nat},
      CountedLoopPrefix c body σ o cost turns →
      ∀ {last : Solidity.Out C σ.H Γ},
      TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n o = .inl last →
      ∃ finalCost, CountedLoopPrefix c body σ last finalCost (turns + n)
  | 0, _, _, _, hp, _, h => by cases h; exact ⟨_, hp⟩
  | n + 1, o, _, _, hp, _, h => by
    simp only [TLoop.iterN, TLoop.step] at h
    cases hc : c.evalT o.st with
    | error error => rw [hc] at h; cases h
    | ok value =>
      cases value with
      | false => rw [hc] at h; cases h
      | true =>
        rw [hc] at h
        cases hs : body.run o.st with
        | error error =>
          simp only [horizonBody, hs, Except.map] at h
          cases h
        | ok next =>
          simp only [horizonBody, hs, Except.map] at h
          obtain ⟨finalCost, hp'⟩ := CountedLoopPrefix.extend_pending n (.next hp hc hs) h
          exact ⟨finalCost, by simpa only [Nat.succ_add, Nat.add_succ] using hp'⟩

theorem countedPrefix_of_iterN_pending {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {n : Nat} {o : Solidity.Out C σ.H Γ}
    (h : TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n
      ⟨σ, List.prefix_refl _⟩ = .inl o) :
    ∃ cost, CountedLoopPrefix c body σ o cost n := by
  simpa only [Nat.zero_add] using CountedLoopPrefix.extend_pending n .start h

/-- Exact initial-cursor room for true-condition turns reached strictly before
`horizon`. A reverting body still requires its reached allocation cost. -/
def FiniteLoopRoom (b frame : Nat) (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine) (horizon : Nat) : Prop :=
  ∀ (o : Solidity.Out C σ.H Γ) (cost turns : Nat),
    CountedLoopPrefix c body σ o cost turns → turns < horizon →
    c.evalT o.st = .ok true →
    AllocationInput b frame (cost + allocationCostProg body o.st) σ base m

theorem LoopRoom.finite {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (room : LoopRoom b frame c body σ base m) (n : Nat) :
    FiniteLoopRoom b frame c body σ base m n :=
  fun o cost _ hp _ hc => room o cost hp.forget hc

theorem finiteLoopRoom_zero (b frame : Nat) (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine) :
    FiniteLoopRoom b frame c body σ base m 0 := by
  intro _ _ turns _ ht _
  omega

/-- Pending means exactly `turns` successful bodies; completion uses strictly
fewer successful bodies because its exit condition consumes a turn. -/
inductive CountedHorizonRelation (L b frame : Nat) (F : Frag Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Δ) (σ : State C Γ) (base : Nat → Fin W) (m₀ : Machine) (turns : Nat) :
    Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ) → Machine ⊕ Out → Prop where
  | more {o m base' cost} (hpref : CountedLoopPrefix c body σ o cost turns)
      (repr : StateRepr L b frame F o.st base' m) (stack : m.stack = m₀.stack)
      (hbase : BaseExtends σ.H base base')
      (grows : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      CountedHorizonRelation L b frame F c body σ base m₀ turns (.inl o) (.inl m)
  | done {o m base' cost count} (hpref : CountedLoopPrefix c body σ o cost count)
      (earlier : count < turns) (stopped : c.evalT o.st = .ok false)
      (repr : StateRepr L b frame F o.st base' m) (stack : m.stack = m₀.stack)
      (hbase : BaseExtends σ.H base base')
      (grows : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
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
  | more hp hr hs he hg => exact .more hp.forget hr hs he hg
  | done hp _ _ hr hs he hg => exact .done hp.forget hr hs he hg
  | revert => exact .revert

/-- One actual condition/body turn, including condition and body reverts. -/
theorem LoopCert.finite_horizon_step {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (cap : b + frameNeedProg body ≤ frame)
    {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost turns : Nat}
    (hpref : CountedLoopPrefix c body σ o cost turns)
    (room : c.evalT o.st = .ok true →
      AllocationInput b frame (cost + allocationCostProg body o.st) σ base m₀)
    (repr : StateRepr L b frame F o.st base' m)
    (stack : m.stack = m₀.stack) (hbase : BaseExtends σ.H base base')
    (grows : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
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
      have ha : AllocationInput b frame (allocationCostProg body o.st) o.st base' m :=
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
      CountedLoopPrefix c body σ o cost turns → StateRepr L b frame F o.st base' m →
      m.stack = m₀.stack → BaseExtends σ.H base base' →
      GrowsAllocator b frame cost σ base m₀ o.st base' m →
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
    (n : Nat) (repr : StateRepr L b frame F σ base m)
    (cap : b + frameNeedProg body ≤ frame)
    (room : FiniteLoopRoom b frame c body σ base m n) :
    CountedHorizonRelation L b frame F c body σ base m n
      (TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ, List.prefix_refl _⟩)
      (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n m) := by
  simpa only [Nat.zero_add] using
    (cert.finite_horizon_iter room cap n 0 (by omega) .start repr rfl
      (BaseExtends.refl base) (fun _ _ ha _ => ha))

/-- Compatibility: consumers of the original public relation can use the
strictly finite capacity interface directly. -/
theorem LoopCert.correct_horizon_of_finite_room {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base m)
    (cap : b + frameNeedProg body ≤ frame)
    (room : FiniteLoopRoom b frame c body σ base m n) :
    HorizonRelation L b frame F c body σ base m
      (TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n ⟨σ, List.prefix_refl _⟩)
      (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n m) :=
  (cert.correct_finite_horizon n repr cap room).forget

end Solidity.Evm.Memory
